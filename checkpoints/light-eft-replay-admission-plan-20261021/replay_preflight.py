"""PROPOSED runner observations only. Not integrated, executed or native-qualified."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import shutil
import signal
import stat
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REL = str(Path(__file__).resolve().relative_to(ROOT))
PROJECTIONS = ('PATH', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH')
ABSENT = ('SHELLOPTS', 'BASHOPTS', 'CDPATH', 'GLOBIGNORE', 'BASH_ENV', 'ENV')
SPECS = ('light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021')
SCRIPT_SHA = 'b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d'
LOOP_SHA = '1fa6ae14282686d2b21fab4e3cdf011b6124c8daed587b2d23a5f42b1e9c5e62'
LIMIT = 64 * 1024**2

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def normal(env, ids):
    require(all(k not in env for k in ABSENT), 'Unadmitted inherited shell-option/startup export')
    require(ids['uid'] == ids['euid'] and ids['gid'] == ids['egid'], 'Real/effective UID or GID differs')
    require(env.get('LEAN_NUM_THREADS') == '1', 'Worker setting differs')
    # All frozen module names are ASCII, but keep the actual locale fixed too.
    require(env.get('LC_ALL', env.get('LANG')) in ('C.UTF-8', 'C.utf8'), 'Unadmitted locale')

def projection(env):
    return {k: env.get(k) for k in PROJECTIONS}  # None and empty remain distinct.

def equivalent(baseline, observed):
    require(baseline['environment'] == observed['environment'], 'Lake/Bash effective environment differs')
    require(baseline['checker'] == observed['checker'], 'Effective pinned checker identity differs')
    require(baseline['tools'] == observed['tools'], 'Pinned toolchain identity differs')

def sig(s):
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_mode, s.st_uid, s.st_gid, s.st_nlink]

def binding(path):
    p = Path(path).absolute()
    chain = []
    for q in [*reversed(p.parents), p]:
        s = q.lstat()
        chain.append(dict(path=str(q), identity=sig(s), link=os.readlink(q) if stat.S_ISLNK(s.st_mode) else None))
    canonical = p.resolve(strict=True)
    fd = os.open(canonical, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as f:
        a = os.fstat(f.fileno())
        require(stat.S_ISREG(a.st_mode) and a.st_nlink >= 1 and a.st_size <= LIMIT, 'Unsafe/oversized bound file')
        data = f.read(LIMIT + 1)
        z = os.fstat(f.fileno())
    require(len(data) <= LIMIT and sig(a) == sig(z) == sig(canonical.lstat()), 'Bound file changed while reading')
    # Parent directory timestamps may change for owned evidence beside inputs.
    for row in chain:
        q = Path(row['path']);s = q.lstat()
        before = row['identity']
        require([s.st_dev, s.st_ino, s.st_mode, s.st_uid, s.st_gid] == [before[i] for i in [0, 1, 5, 6, 7]], 'Bound path component changed')
        require((os.readlink(q) if stat.S_ISLNK(s.st_mode) else None) == row['link'], 'Bound symlink changed')
    stable_chain = [dict(path=x['path'], identity=[x['identity'][i] for i in [0, 1, 5, 6, 7]], link=x['link']) for x in chain]
    return dict(path=str(p), canonical=str(canonical), bytes=len(data), sha256=sha(data), identity=sig(z), chain=stable_chain)

def git(*args):
    # Same read-only Git boundary as the existing exact-source controllers.
    return subprocess.run(['git', *args], cwd=ROOT, check=True, capture_output=True, timeout=10).stdout

def checked_sources():
    critical = [REL, 'scripts/KernelCheck.sh', '.github/workflows/lean.yml', 'lakefile.toml', 'lean-toolchain', 'lake-manifest.json']
    raw = {p: (ROOT / p).read_bytes() for p in critical}
    require(sha(raw['scripts/KernelCheck.sh']) == SCRIPT_SHA, 'Proposed replay script differs')
    for p, b in raw.items():
        require(b == git('show', 'HEAD:' + p), 'Admission input differs from exact Git source')
    for name in SPECS:
        p = 'checkpoints/' + name + '/ci-spec.json'
        b = (ROOT / p).read_bytes();require(b == git('show', 'HEAD:' + p), 'Specification differs from Git')
        rows = {r['path']: r for r in json.loads(b)['engine_files']}
        for rel in [REL, 'scripts/KernelCheck.sh', '.github/workflows/lean.yml']:
            require(rows.get(rel) == dict(path=rel, bytes=len(raw[rel]), sha256=sha(raw[rel])), 'Admission source is not bound in every existing specification')
    return {p: binding(ROOT / p) for p in critical}

def context(env):
    path = ROOT / 'checkpoints/light-eft-sequential-validation-schedule-20261021/workflow_identity.py'
    spec = importlib.util.spec_from_file_location('_replay_admission_identity', path)
    module = importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    head = git('rev-parse', 'HEAD').decode().strip()
    ci = module.identity(env, head)
    require(env.get('LIGHTEFT_VALIDATION_ROLE') == 'full' and Path.cwd().resolve() == ROOT, 'Not the exact full replay job/cwd')
    return dict(CI_identity=ci, workspace=str(ROOT), boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
                namespaces={n: os.readlink('/proc/self/ns/' + n) for n in ['pid', 'mnt', 'cgroup']})

def platform(env):
    ids = dict(uid=os.getuid(), euid=os.geteuid(), gid=os.getgid(), egid=os.getegid())
    normal(env, ids)
    return dict(ids=ids, bash=binding('/bin/bash'), python=binding('/usr/bin/python3'), sources=checked_sources())

def root(env):
    require(env.get('GITHUB_RUN_ID', '').isdecimal() and env.get('GITHUB_RUN_ATTEMPT', '').isdecimal(), 'Bad run/attempt')
    parent = Path(env['RUNNER_TEMP'])
    require(parent.is_absolute() and parent.is_dir() and not parent.is_symlink(), 'Bad runner temporary root')
    return parent / ('light-eft-replay-admission-' + env['GITHUB_RUN_ID'] + '-' + env['GITHUB_RUN_ATTEMPT'])

def owned_root(folder):
    s = folder.lstat()
    require(stat.S_ISDIR(s.st_mode) and stat.S_IMODE(s.st_mode) == 0o700 and s.st_uid == os.getuid(), 'Unsafe admission directory')

def write(folder, name, data):
    owned_root(folder)
    raw = (json.dumps(data, sort_keys=True, indent=2) + '\n').encode()
    require(len(raw) <= 1024**2, 'Admission report too large')
    fd = os.open(folder / name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'wb') as f:
        f.write(raw);f.flush();os.fsync(f.fileno())

def load(folder, name):
    owned_root(folder)
    path = folder / name;s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and stat.S_IMODE(s.st_mode) == 0o600 and s.st_uid == os.getuid() and s.st_nlink == 1, 'Unsafe admission record')
    require(s.st_size <= 1024**2, 'Oversized admission record')
    before = binding(path);data = json.loads(path.read_text());require(binding(path) == before, 'Admission record changed')
    return data, before

def fresh_boot(folder, env):
    record, row = load(folder, 'bootstrap.json')
    require(record['context'] == context(env) and record['platform'] == platform(env), 'Runner/source/platform changed after bootstrap')
    return record, row

def observe_lake(env):
    tool = Path(env.get('LEAN_SYSROOT', ''))
    require(tool.is_absolute(), 'Missing actual Lake sysroot')
    spec = json.loads((ROOT / 'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci-spec.json').read_text())
    require(spec['toolchain'] == 'leanprover/lean4:v4.34.0', 'Toolchain contract differs')
    tools = {n: binding(tool / 'bin' / n) for n in ['lean', 'leanchecker', 'lake']}
    require(all(tools[n]['sha256'] == spec['tool_hashes'][n] for n in ['lean', 'leanchecker']), 'Actual Lake tool hashes differ')
    require(env.get('LAKE') and Path(env['LAKE']).resolve() == Path(tools['lake']['canonical']), 'Lake environment identifies another Lake executable')
    selected = shutil.which('leanchecker', path=env.get('PATH', ''))
    require(selected is not None, 'Checker not executable/resolvable')
    checker = binding(selected)
    require(checker['canonical'] == tools['leanchecker']['canonical'] and checker['identity'] == tools['leanchecker']['identity'], 'PATH selects a different checker')
    return dict(environment=projection(env), checker=checker, tools=tools)

def bootstrap(env):
    folder = root(env);folder.mkdir(mode=0o700, exist_ok=False)
    selected = shutil.which('lake', path=env.get('PATH', ''))
    require(selected is not None, 'No installed Lake/elan carrier')
    write(folder, 'bootstrap.json', dict(context=context(env), platform=platform(env), observed_ns=time.monotonic_ns(),
          inherited_environment=projection(env), lake_launcher=binding(selected),
          qualification='FRESH_RUNNER_LAUNCHER_ADMISSION_ONLY; no native verification or execution permission'))

def command(argv):
    require(len(argv) == 8 and argv[:7] == ['/bin/bash', '--noprofile', '--norc', '-p', '-euo', 'pipefail', '-c'], 'Unreviewed inner-shell command')
    require(sha(argv[7].encode()) == LOOP_SHA, 'Unreviewed replay-loop body')

def before_lake(env, argv):
    command(argv)
    folder = root(env);boot, boot_row = fresh_boot(folder, env)
    require(projection(env) == boot['inherited_environment'], 'Inherited environment changed before Lake')
    selected = shutil.which('lake', path=env.get('PATH', ''))
    require(selected and binding(selected) == boot['lake_launcher'], 'Lake/elan carrier changed')
    write(folder, 'before-lake.json', dict(context=boot['context'], bootstrap=boot_row, inherited_environment=projection(env),
          lake_launcher=boot['lake_launcher'], observed_ns=time.monotonic_ns()))
    signal.setitimer(signal.ITIMER_REAL, 0)
    os.execv(selected, [selected, 'env', '/usr/bin/python3', '-I', '-B', str(Path(__file__).resolve()), 'enter', *argv])

def enter(env, argv):
    command(argv)
    folder = root(env);boot, boot_row = fresh_boot(folder, env)
    before, before_row = load(folder, 'before-lake.json')
    require(before['context'] == boot['context'] and before['bootstrap'] == boot_row and
            before['lake_launcher'] == boot['lake_launcher'] and before['inherited_environment'] == boot['inherited_environment'],
            'Before-Lake context differs')
    baseline = observe_lake(env)
    write(folder, 'lake-baseline.json', dict(context=boot['context'], bootstrap=boot_row, before_lake=before_row, baseline=baseline, observed_ns=time.monotonic_ns()))
    signal.setitimer(signal.ITIMER_REAL, 0)  # The admission deadline never becomes a replay deadline.
    os.execv(argv[0], argv)

def verify(env, flags, version):
    require('p' in flags and version.startswith(('4.', '5.')), 'Unsupported inner Bash state/version')
    folder = root(env);boot, boot_row = fresh_boot(folder, env)
    saved, baseline_row = load(folder, 'lake-baseline.json')
    before, before_row = load(folder, 'before-lake.json')
    require(saved['context'] == boot['context'] and saved['bootstrap'] == boot_row and saved['before_lake'] == before_row,
            'Baseline/bootstrap binding differs')
    observed = observe_lake(env);equivalent(saved['baseline'], observed)
    write(folder, 'verified.json', dict(context=boot['context'], bootstrap=boot_row, baseline=baseline_row, observed=observed,
          bash_flags=flags, bash_version=version, verified_ns=time.monotonic_ns(), qualification='Environment/checker equality only; kernel replay still mandatory'))

def main():
    def timeout(*_):
        raise TimeoutError('Replay admission exceeded 90 seconds')
    require(signal.getitimer(signal.ITIMER_REAL) == (0.0, 0.0), 'Existing timer would be replaced')
    previous = signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 90)
    try:
        env = dict(os.environ);mode = sys.argv[1]
        if mode == 'bootstrap':bootstrap(env)
        elif mode == 'before-lake':before_lake(env, sys.argv[2:])
        elif mode == 'enter':enter(env, sys.argv[2:])
        elif mode == 'verify':verify(env, sys.argv[2], sys.argv[3])
        else:raise ValueError('Unknown replay admission phase')
    except BaseException as error:
        try:
            folder = root(dict(os.environ))
            if folder.exists():
                phase = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] in ['bootstrap', 'before-lake', 'enter', 'verify'] else 'unknown'
                write(folder, 'failure-' + phase + '.json', dict(error=repr(error), observed_ns=time.monotonic_ns()))
        except BaseException:
            pass
        raise  # Never turn missing evidence, timeout or record failure into a fallback loop.
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0);signal.signal(signal.SIGALRM, previous)

if __name__ == '__main__':
    main()
