#!/usr/bin/env python3
"""One compiler admission gate for the isolated Greedy CI branch.

Only a disposable copy of the selected toolchain is changed. Lake may queue
jobs, but every Lean/IR/checker/C frontend must hold the same inherited flock.
Nested compiler launches fail closed instead of bypassing or deadlocking it.
"""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time
import uuid

TOOLS = ("lean", "leanir", "leanchecker", "clang")
EXPECTED_SOURCES = {
    "ChainStrictJoinGuardV2": "d55adc469bdd8ef84111a36b55574fef9bd6fa765305c47d9515f8a85c83ee3b",
    "ChainSharedPivotGuardV2": "c3f7a914d6b25fa6de6c553556f5a8b4067fed5f192aa1c0b14d4a4fa4de9688",
}


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def output(*args):
    return subprocess.check_output(args, text=True).strip()


def wrapper_text(state, tool):
    command = [sys.executable, str(Path(__file__).resolve()), "invoke",
               "--state", str(state), "--tool", tool, "--"]
    return "\n".join([
        "#!/usr/bin/env bash", "set -euo pipefail",
        'if [[ -n "${GREEDY_SERIAL_ACTIVE:-}" ]]; then',
        '  echo "Nested compiler invocation rejected by serial admission" >&2',
        "  exit 97", "fi",
        "exec 9>>" + shlex.quote(str(state / "compiler.lock")),
        shlex.quote(shutil.which("flock") or "/usr/bin/flock") + " --exclusive 9",
        "exec " + shlex.join(command) + ' "$@"', "",
    ])


def setup(state):
    if not shutil.which("flock"):
        raise RuntimeError("flock is required")
    if Path("lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.0":
        raise RuntimeError("Unexpected toolchain")
    source = Path(output("lean", "--print-prefix")).resolve()
    if output("lean", "--githash") != "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b":
        raise RuntimeError("Unexpected Lean binary revision")
    state.mkdir(parents=True, exist_ok=False)
    mirror = state / "toolchain"
    shutil.copytree(source, mirror, symlinks=True)
    (state / "compiler.lock").touch(exist_ok=False)
    metadata = {"source_sysroot": str(source), "mirror": str(mirror),
                "helper_sha256": digest(__file__), "tools": {}}
    for tool in TOOLS:
        path = mirror / "bin" / tool
        if not path.is_file() or path.is_symlink():
            raise RuntimeError(f"Expected native tool binary: {path}")
        real = path.with_name(tool + ".serial-real")
        path.rename(real)
        path.write_text(wrapper_text(state, tool))
        path.chmod(0o755)
        metadata["tools"][tool] = {"real": str(real), "real_sha256": digest(real),
                                   "wrapper": str(path), "wrapper_sha256": digest(path)}
    (state / "metadata.json").write_text(json.dumps(metadata, sort_keys=True, indent=2) + "\n")
    name = "greedy-serial-" + os.environ["GITHUB_RUN_ID"] + "-" + os.environ["GITHUB_RUN_ATTEMPT"]
    subprocess.run(["elan", "toolchain", "link", name, str(mirror)], check=True)
    values = {"ELAN_TOOLCHAIN": name, "LEAN_SYSROOT": str(mirror),
              "LAKE_OVERRIDE_LEAN": "true", "LEAN": str(mirror / "bin/lean"),
              "LEAN_NUM_THREADS": "1", "GREEDY_SERIAL_STATE": str(state)}
    with open(os.environ["GITHUB_ENV"], "a") as f:
        for key, value in values.items():
            f.write(f"{key}={value}\n")
    with open(os.environ["GITHUB_PATH"], "a") as f:
        f.write(str(mirror / "bin") + "\n")
    print(json.dumps({"serial_toolchain_ready": values, "metadata_sha256": digest(state / "metadata.json")}))


def invoke(state, tool, args):
    metadata = json.loads((state / "metadata.json").read_text())
    spec = metadata["tools"][tool]
    if digest(__file__) != metadata["helper_sha256"]:
        raise RuntimeError("Serial helper changed")
    if digest(spec["real"]) != spec["real_sha256"]:
        raise RuntimeError("Underlying tool changed")
    owned = os.fstat(9)
    expected = (state / "compiler.lock").stat()
    if (owned.st_dev, owned.st_ino) != (expected.st_dev, expected.st_ino):
        raise RuntimeError("Wrong admission descriptor")
    fcntl.flock(9, fcntl.LOCK_EX | fcntl.LOCK_NB)
    token = uuid.uuid4().hex
    command = [spec["real"], *args]
    def event(kind, **fields):
        with (state / "events.jsonl").open("a") as f:
            f.write(json.dumps(dict(kind=kind, token=token, tool=tool,
                                   time_ns=time.time_ns(), **fields), sort_keys=True) + "\n")
    event("started", command=command, controller_pid=os.getpid())
    env = dict(os.environ, GREEDY_SERIAL_ACTIVE=token, LEAN_NUM_THREADS="1")
    try:
        # The child keeps the lock even if its controller is interrupted.
        child = subprocess.Popen(command, env=env, pass_fds=(9,))
        code = child.wait()
    except BaseException:
        event("interrupted")
        raise
    event("finished", exit_code=code)
    return code if code >= 0 else 128 - code


def verify(state, commit, dependencies):
    if len(commit) != 40 or any(c not in "0123456789abcdef" for c in commit):
        raise RuntimeError("Expected a full commit SHA")
    if output("git", "rev-parse", "HEAD") != commit:
        raise RuntimeError("Checkout is not the requested exact commit")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], check=True)
    for name, expected in EXPECTED_SOURCES.items():
        source = Path("Greedy Algorithms for Shortcut Sets and Hopsets/GreedyShortcuts") / (name + ".lean")
        if digest(source) != expected:
            raise RuntimeError(f"Unexpected source bytes: {source}")
    metadata = json.loads((state / "metadata.json").read_text())
    if output("lean", "--print-prefix") != metadata["mirror"]:
        raise RuntimeError("Direct Lean bypasses serial toolchain")
    if output("lake", "env", "printenv", "LEAN") != str(Path(metadata["mirror"]) / "bin/lean"):
        raise RuntimeError("Lake bypasses serial toolchain")
    if dependencies:
        for package in json.loads(Path("lake-manifest.json").read_text())["packages"]:
            path = Path(".lake/packages") / package["name"]
            if output("git", "-C", str(path), "rev-parse", "HEAD") != package["rev"]:
                raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
    print(json.dumps({"verified_exact_commit": commit, "dependencies_checked": dependencies}))


def report(state):
    metadata = json.loads((state / "metadata.json").read_text())
    if digest(__file__) != metadata["helper_sha256"]:
        raise RuntimeError("Serial helper changed")
    for spec in metadata["tools"].values():
        if digest(spec["wrapper"]) != spec["wrapper_sha256"] or digest(spec["real"]) != spec["real_sha256"]:
            raise RuntimeError("Serial toolchain changed")
    events = [json.loads(line) for line in (state / "events.jsonl").read_text().splitlines()]
    active = None
    completed = set()
    tools = set()
    for event in events:
        if event["kind"] == "started":
            if active is not None or event["token"] in completed:
                raise RuntimeError("Overlapping or repeated compiler admission")
            active = event["token"]
            tools.add(event["tool"])
        elif event["kind"] == "finished":
            if active != event["token"] or event["exit_code"] != 0:
                raise RuntimeError("Unmatched or unsuccessful compiler invocation")
            completed.add(active)
            active = None
        else:
            raise RuntimeError("Interrupted compiler invocation")
    if active is not None or not {"lean", "leanchecker"}.issubset(tools):
        raise RuntimeError("Incomplete compiler or kernel replay evidence")
    print(json.dumps({"serial_invocations": len(completed), "maximum_concurrent": 1,
                      "tools": sorted(tools), "events_sha256": digest(state / "events.jsonl")}))


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("setup", "invoke", "verify", "report"):
        sub = commands.add_parser(name)
        sub.add_argument("--state", type=Path, required=True)
        if name == "invoke":
            sub.add_argument("--tool", choices=TOOLS, required=True)
            sub.add_argument("args", nargs=argparse.REMAINDER)
        if name == "verify":
            sub.add_argument("--commit", required=True)
            sub.add_argument("--dependencies", action="store_true")
    args = parser.parse_args()
    if args.command == "setup": setup(args.state.resolve())
    elif args.command == "invoke":
        tail = args.args[1:] if args.args[:1] == ["--"] else args.args
        return invoke(args.state.resolve(), args.tool, tail)
    elif args.command == "verify": verify(args.state.resolve(), args.commit, args.dependencies)
    else: report(args.state.resolve())
    return 0


if __name__ == "__main__":
    sys.exit(main())
