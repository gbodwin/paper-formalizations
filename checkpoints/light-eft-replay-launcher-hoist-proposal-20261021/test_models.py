"""Shell/launcher models only. Fake Lake/checker; no Lean binary or CI access."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = 'd031f60c681650e48b409115adaffd240ec6493a'
ROWS = json.loads((HERE / 'MODULES.json').read_text())
OLD = subprocess.check_output(['git', 'show', BASE + ':scripts/KernelCheck.sh'], cwd=ROOT)
NEW = (HERE / 'PROPOSED-KernelCheck.sh').read_bytes()
LIBRARIES = list(dict.fromkeys(r['module'].split('.')[0] for r in ROWS))
SMALL = [r for lib in LIBRARIES for r in [x for x in ROWS if x['module'].startswith(lib + '.')][:3]]
KEYS = ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB',
        'MIMALLOC_ARENA_RESERVE', 'LANG', 'LC_ALL', 'LD_LIBRARY_PATH', 'MODEL_SENTINEL']

STUB = '''#!/usr/bin/env python3
from pathlib import Path
import fcntl,json,os,subprocess,sys
role=Path(sys.argv[0]).name
base=Path(os.environ['MODEL_ROOT'])
def write(name,row):
 with (base/name).open('a') as f:f.write(json.dumps(row,sort_keys=True)+'\\n')
if role=='lake':
 assert sys.argv[1]=='env'
 write('lake.jsonl',{'argv':sys.argv[1:]})
 if os.environ.get('MODEL_LAKE_FAIL')=='1':sys.exit(53)
 env=dict(os.environ)
 env.update(LEAN_PATH='/model/objects with spaces:/model/packages',LEAN_SRC_PATH='/model/source',
            LEAN_SYSROOT='/model/toolchain',LD_LIBRARY_PATH='/model/shared',MODEL_SENTINEL='set by fake Lake')
 cmd=sys.argv[2:]
 assert cmd and (cmd[0]=='leanchecker' or Path(cmd[0]).name=='bash')
 sys.exit(subprocess.run(cmd,env=env).returncode)
assert role=='leanchecker'
with (base/'single-checker.lock').open('w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 row={'argv':sys.argv[1:],'cwd':str(Path.cwd().relative_to(base)),
      'environment':{k:os.environ.get(k) for k in json.loads(os.environ['MODEL_KEYS'])}}
 write('checker.jsonl',row)
 assert len(sys.argv)==3 and sys.argv[1]=='-v'
 module=sys.argv[2]
 print('replaying '+module,flush=True)
 if module==os.environ.get('MODEL_FAIL_MODULE'):
  print('model checker rejection: '+module,file=sys.stderr,flush=True);sys.exit(37)
'''

def read_lines(path):
    return [json.loads(x) for x in path.read_text().splitlines()] if path.exists() else []

def model(script, rows, *, failure=None, lake_fail=False, extra=None, function=False, startup_hook=False):
    with tempfile.TemporaryDirectory(prefix='light-eft-launcher-model-', dir='/tmp') as temp:
        base = Path(temp)
        project = base / 'repo'
        project.mkdir()
        for row in rows:
            p = project / row['source']
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('-- synthetic source path only; never compiled\n')
        if extra:
            for rel in extra:
                p = project / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text('-- synthetic path only\n')
        bin_dir = base / 'bin'
        bin_dir.mkdir()
        for name in ['lake', 'leanchecker']:
            p = bin_dir / name
            p.write_text(STUB)
            p.chmod(0o700)
        script_path = base / 'driver.sh'
        script_path.write_bytes(script)
        env = dict(os.environ)
        for key in ['BASH_ENV', 'ENV', 'SHELLOPTS', 'BASHOPTS', 'GLOBIGNORE']:
            env.pop(key, None)
        env.update(PATH=str(bin_dir) + ':' + os.environ['PATH'], MODEL_ROOT=str(base),
                   MODEL_KEYS=json.dumps(KEYS), LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='65536',
                   MIMALLOC_ARENA_RESERVE='128MiB', LANG='C.UTF-8', LC_ALL='C.UTF-8')
        if failure:
            env['MODEL_FAIL_MODULE'] = failure
        if lake_fail:
            env['MODEL_LAKE_FAIL'] = '1'
        if function:
            env['BASH_FUNC_leanchecker%%'] = '() { echo forbidden-shell-function; return 99; }'
        if startup_hook:
            hook = base / 'startup-hook.sh'
            hook.write_text(': # already sourced by the outer shell; new inner sourcing is forbidden\n')
            env['BASH_ENV'] = str(hook)
        result = subprocess.run([shutil.which('bash'), str(script_path)], cwd=project,
                                env=env, capture_output=True, text=True, timeout=60)
        return dict(exit=result.returncode, stdout=result.stdout, stderr=result.stderr,
                    checker=read_lines(base / 'checker.jsonl'), lake=read_lines(base / 'lake.jsonl'))

class Models(unittest.TestCase):
    def compare(self, rows, **kwargs):
        a, b = model(OLD, rows, **kwargs), model(NEW, rows, **kwargs)
        for key in ['exit', 'stdout', 'stderr', 'checker']:
            self.assertEqual(a[key], b[key], key)
        self.assertEqual(len(a['lake']), len(a['checker']) if not kwargs.get('lake_fail') else 1)
        self.assertEqual(len(b['lake']), 1)
        return a, b

    def test_all_567_exact_targets_arguments_environment_and_order(self):
        self.assertEqual(len(ROWS), 567)
        a, b = self.compare(ROWS)
        self.assertEqual(a['exit'], 0)
        self.assertEqual([x['argv'] for x in b['checker']], [['-v', r['module']] for r in ROWS])
        self.assertEqual(len(a['lake']), 567)

    def test_first_failure_stops(self):
        a, b = self.compare(SMALL, failure=SMALL[0]['module'])
        self.assertEqual(a['exit'], 37)
        self.assertEqual(len(b['checker']), 1)

    def test_middle_failure_stops(self):
        a, b = self.compare(SMALL, failure=SMALL[7]['module'])
        self.assertEqual(a['exit'], 37)
        self.assertEqual(len(b['checker']), 8)

    def test_last_failure_is_not_swallowed(self):
        a, b = self.compare(SMALL, failure=SMALL[-1]['module'])
        self.assertEqual(a['exit'], 37)
        self.assertEqual(len(b['checker']), len(SMALL))

    def test_lake_setup_failure_runs_no_checker(self):
        a, b = self.compare(SMALL, lake_fail=True)
        self.assertEqual(a['exit'], 53)
        self.assertEqual(b['checker'], [])

    def test_exported_checker_function_cannot_replace_official_binary(self):
        a, b = self.compare(SMALL, function=True)
        self.assertEqual(a['exit'], 0)
        self.assertNotIn('forbidden-shell-function', b['stdout'])

    def test_space_in_module_is_one_argument(self):
        extra = ['A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/VFTSpanners/Space Name.lean']
        a, b = self.compare(SMALL, extra=extra)
        self.assertEqual(a['exit'], 0)
        self.assertIn(['-v', 'VFTSpanners.Space Name'], [x['argv'] for x in b['checker']])

    def test_nonlean_and_nested_files_are_not_added(self):
        extra = ['A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/VFTSpanners/ignored.txt',
                 'A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/VFTSpanners/Nested/ignored.lean']
        a, b = self.compare(SMALL, extra=extra)
        self.assertEqual([x['argv'][1] for x in b['checker']], [r['module'] for r in SMALL])

    def test_shell_syntax_without_execution(self):
        result = subprocess.run([shutil.which('bash'), '-n', str(HERE / 'PROPOSED-KernelCheck.sh')], capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_extra_shell_startup_hook_fails_closed(self):
        b = model(NEW, SMALL, startup_hook=True)
        self.assertEqual(b['exit'], 2)
        self.assertEqual(b['checker'], [])
        self.assertEqual(b['lake'], [])
        self.assertIn('absent shell startup hooks', b['stderr'])

    def test_source_carriers_and_prefix_free_targets(self):
        names = [r['module'] for r in ROWS]
        self.assertEqual(len(names), len(set(names)))
        self.assertFalse(any(b.startswith(a + '.') for a in names for b in names))
        for row in ROWS:
            raw = (ROOT / row['source']).read_bytes()
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest()), (row['bytes'], row['sha256']))

    def test_production_workflow_gates_and_limits_are_untouched(self):
        for rel in ['scripts/KernelCheck.sh', '.github/workflows/lean.yml',
                    '.github/workflows/light-eft-fair-bit-focused.yml',
                    'checkpoints/light-eft-sequential-validation-schedule-20261021/acceptance.py']:
            self.assertEqual((ROOT / rel).read_bytes(), subprocess.check_output(['git', 'show', BASE + ':' + rel], cwd=ROOT))

if __name__ == '__main__':
    unittest.main(verbosity=2)
