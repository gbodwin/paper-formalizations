"""Static literal/hash regression: no shell, admission, policy or native execution."""
from pathlib import Path
import ast, hashlib, json, subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = '307414c84ebdbe7395f0c08d3f27ecf0d66ec7c5'
SCRIPT = 'scripts/KernelCheck.sh'
HELPER = 'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py'
POLICY = 'checkpoints/light-eft-sequential-validation-schedule-20261021/workflow_identity.py'
SCRIPT_SHA = 'b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d'
OLD_LOOP = '53717997a6a67054021e6b82a61113676e62b2f2ed134868ffd622eb86874bbb'
LOOP = '1fa6ae14282686d2b21fab4e3cdf011b6124c8daed587b2d23a5f42b1e9c5e62'
OLD_HELPER = '72f33cd3676552f902cc7361ae805186971bbdf07e1f3fcc13a45a81b3797425'
HELPER_SHA = '2bcbe3ba3a4154d61ff01a19b0dfc615a6b50f64b3eb09020765a299af7fe4be'
NAMES = ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

script = (ROOT / SCRIPT).read_bytes()
assert script == git('show', BASE + ':' + SCRIPT) and sha(script) == SCRIPT_SHA
# Bash single quotes preserve every byte between these quotes, including LF.
# Exactly one opener/closer and no embedded quote make this literal extraction
# independent of executing Bash or reproducing production command(argv).
parts = script.split(b"-c '")
assert len(parts) == 2
body_and_tail = parts[1].split(b"'\n    ;;", 1)
assert len(body_and_tail) == 2
literal = body_and_tail[0]
assert b"'" not in literal and literal.startswith(b'\n') and literal.endswith(b'\n')
assert len(literal) == 981 and sha(literal) == LOOP
assert literal.decode('utf-8').encode('utf-8') == literal
assert len(literal[1:]) == 980 and sha(literal[1:]) == OLD_LOOP
variants = {
    'old_missing_leading_LF': literal[1:],
    'extra_leading_LF': b'\n' + literal,
    'missing_final_LF': literal[:-1],
    'extra_final_LF': literal + b'\n',
    'CRLF': literal.replace(b'\n', b'\r\n'),
    'leading_space': b' ' + literal,
    'trailing_space': literal + b' ',
    'changed_checker': literal.replace(b'command leanchecker', b'command true'),
    'missing_first_verification': b'\n' + literal.split(b'\n', 2)[2],
}
assert all(raw != literal and sha(raw) != LOOP for raw in variants.values())
helper = (ROOT / HELPER).read_bytes()
old_helper = git('show', BASE + ':' + HELPER)
assert old_helper.count(("LOOP_SHA = '" + OLD_LOOP + "'").encode()) == 1
assert helper == old_helper.replace(("LOOP_SHA = '" + OLD_LOOP + "'").encode(), ("LOOP_SHA = '" + LOOP + "'").encode(), 1)
assert sha(helper) == HELPER_SHA
constants = {n.targets[0].id: ast.literal_eval(n.value) for n in ast.parse(helper).body
             if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
             and n.targets[0].id in ['SCRIPT_SHA', 'LOOP_SHA']}
assert constants == dict(SCRIPT_SHA=SCRIPT_SHA, LOOP_SHA=LOOP)
policy = (ROOT / POLICY).read_bytes()
expected = git('show', BASE + ':' + POLICY).replace(OLD_HELPER.encode(), HELPER_SHA.encode()).replace(OLD_LOOP.encode(), LOOP.encode())
expected = expected.replace(b'parts=script.split(b"-c \'\\n")', b'parts=script.split(b"-c \'")')
assert policy == expected
ast.parse(policy)
regular = recursive = 0
for name in NAMES:
    rel = 'checkpoints/' + name + '/ci-spec.json'
    before = json.loads(git('show', BASE + ':' + rel))
    after = json.loads((ROOT / rel).read_text())
    old_engine, engine = before.pop('engine_files'), after.pop('engine_files')
    assert before == after
    assert len(engine) == len({r['path'] for r in engine})
    assert {r['path'] for r in engine} == {r['path'] for r in old_engine}
    sources = after['sources']
    sources = list(sources.values()) if isinstance(sources, dict) else sources
    regular += len(sources) + len(after['dependencies']) + len(engine)
    def walk(value):
        global recursive
        if isinstance(value, dict):
            if isinstance(value.get('path'), str) and 'bytes' in value and 'sha256' in value:
                raw = (ROOT / value['path']).read_bytes()
                assert len(raw) == value['bytes'] and sha(raw) == value['sha256']
                recursive += 1
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)
    walk(json.loads((ROOT / rel).read_text()))
assert regular == 1034 and recursive == 1041
allowed = {HELPER, POLICY, *['checkpoints/' + n + '/ci-spec.json' for n in NAMES]}
prefix = str(HERE.relative_to(ROOT)) + '/'
changed = git('diff', '--name-only', BASE).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(prefix) for p in changed)
git('diff', '--check', BASE)
print(json.dumps(dict(status='STATIC_LITERAL_SOURCE_HASH_PASS', literal_bytes=len(literal), literal_sha256=LOOP,
                      old_counterexample_sha256=OLD_LOOP, negative_variants=len(variants), regular_rows=regular,
                      recursive_rows=recursive, shell_admission_Lake_checker_or_native_execution=False), sort_keys=True))
