"""Fake Lake/checker models on host Bash only; never invokes Lean or CI."""
from pathlib import Path
import fcntl
import importlib.util
import json
import os
import signal
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PRIOR = HERE.parent / 'light-eft-replay-launcher-hoist-proposal-20261021'
ROWS = json.loads((PRIOR / 'MODULES.json').read_text())
LIBS = list(dict.fromkeys(r['module'].split('.')[0] for r in ROWS))
SMALL = [r for lib in LIBS for r in [x for x in ROWS if x['module'].startswith(lib + '.')][:3]]
NEW = (HERE / 'PROPOSED-KernelCheck.sh').read_bytes()
V1 = (PRIOR / 'PROPOSED-KernelCheck.sh').read_bytes()
NAMES = ['exec', 'hash', 'command', 'set', 'printf', 'exit', 'lake', 'leanchecker', 'builtin',
         'command_not_found_handle', '/bin/bash', 'test', 'true', 'false', 'eval', 'source',
         'trap', 'unset', 'enable', 'declare', 'readonly']
KEYS = ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB',
        'MIMALLOC_ARENA_RESERVE', 'LANG', 'LC_ALL', 'MODEL_SENTINEL']
SHELL = '/bin/bash --noprofile --norc -p -e -o pipefail {0}'
RUN = '/bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh'

STUB = r'''#!/usr/bin/env python3
from pathlib import Path
import fcntl,json,os,signal,subprocess,sys
base=Path(os.environ['MODEL_ROOT']);role=Path(sys.argv[0]).name
def write(name,data):
 with (base/name).open('a') as f:f.write(json.dumps(data,sort_keys=True)+'\n')
if role=='lake':
 assert sys.argv[1]=='env'
 write('lake.jsonl',{'argv':sys.argv[1:]})
 if os.environ.get('MODEL_LAKE_FAIL')=='1':sys.exit(53)
 env=dict(os.environ)
 env.update(LEAN_PATH='/model/objects with spaces:/model/packages',LEAN_SRC_PATH='/model/source',
            LEAN_SYSROOT='/model/toolchain',MODEL_SENTINEL='set by fake Lake')
 env.update(json.loads(os.environ.get('MODEL_AFTER_LAKE','{}')))
 try:code=subprocess.run(sys.argv[2:],env=env).returncode
 except FileNotFoundError:code=127
 except PermissionError:code=126
 sys.exit(code if code>=0 else 128-code)
assert role=='leanchecker'
with (base/'single-checker.lock').open('w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 row={'argv':sys.argv[1:],'cwd':str(Path.cwd().relative_to(base)),'pid':os.getpid(),
      'uid':os.getuid(),'euid':os.geteuid(),
      'environment':{k:os.environ.get(k) for k in json.loads(os.environ['MODEL_KEYS'])}}
 write('checker.jsonl',row)
 assert len(sys.argv)==3 and sys.argv[1]=='-v'
 print('replaying '+sys.argv[2],flush=True)
 if sys.argv[2]==os.environ.get('MODEL_FAIL_MODULE'):
  if os.environ.get('MODEL_SIGNAL'):os.kill(os.getpid(),int(os.environ['MODEL_SIGNAL']))
  sys.exit(int(os.environ.get('MODEL_EXIT','37')))
'''

def functions(names):
    return {'BASH_FUNC_' + name + '%%': '() { /usr/bin/touch "$MODEL_ROOT/intercepted-' + str(i) + '"; return 0; }'
            for i, name in enumerate(names)}

def valid_contract(shell, run):
    return shell == SHELL and run == RUN

def model(rows, *, imported=(), after=(), exit_code=None, sig=None, fail_index=7,
          missing=False, nonexec=False, hook=None, after_hook=False,
          lake_fail=False, script=NEW, entry='trusted', forged_shelopts=False):
    with tempfile.TemporaryDirectory(prefix='light-eft-privileged-model-', dir='/tmp') as temp:
        base = Path(temp)
        repo = base / 'repo'
        (repo / 'scripts').mkdir(parents=True)
        path = repo / 'scripts/KernelCheck.sh'
        path.write_bytes(script)
        path.chmod(0o700)
        for row in rows:
            source = repo / row['source']
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('-- model path only; never compiled\n')
        binary = base / 'bin'
        binary.mkdir()
        (binary / 'python3').symlink_to(sys.executable)
        for name in ['lake', 'leanchecker']:
            if name == 'leanchecker' and missing:
                continue
            p = binary / name
            p.write_text(STUB)
            p.chmod(0o600 if name == 'leanchecker' and nonexec else 0o700)
        env = {k: v for k, v in os.environ.items() if not k.startswith('BASH_FUNC_')}
        for name in ['BASH_ENV', 'ENV', 'SHELLOPTS', 'BASHOPTS', 'GLOBIGNORE', 'CDPATH']:
            env.pop(name, None)
        env.update(PATH=str(binary), MODEL_ROOT=str(base), MODEL_KEYS=json.dumps(KEYS),
                   LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='65536', MIMALLOC_ARENA_RESERVE='128MiB',
                   LANG='C.UTF-8', LC_ALL='C.UTF-8')
        env.update(functions(imported))
        injected = functions(after)
        if hook or after_hook:
            startup = base / 'startup.sh'
            startup.write_text('/usr/bin/touch "$MODEL_ROOT/startup-ran"\n')
            if hook:
                env[hook] = str(startup)
            if after_hook:
                injected['BASH_ENV'] = str(startup)
        env['MODEL_AFTER_LAKE'] = json.dumps(injected)
        if exit_code is not None or sig is not None:
            env.update(MODEL_FAIL_MODULE=rows[fail_index]['module'], MODEL_EXIT=str(exit_code or 37))
        if sig is not None:
            env['MODEL_SIGNAL'] = str(sig)
        if lake_fail:
            env['MODEL_LAKE_FAIL'] = '1'
        if forged_shelopts:
            env['SHELLOPTS'] = 'privileged'
        if entry == 'trusted':
            wrapper = base / 'step.sh'
            wrapper.write_text(RUN + '\n')
            argv = ['/bin/bash', '--noprofile', '--norc', '-p', '-e', '-o', 'pipefail', str(wrapper)]
        elif entry == 'shebang':
            argv = [str(path)]
        elif entry == 'unprivileged':
            argv = ['/bin/bash', '--noprofile', '--norc', str(path)]
        else:
            raise ValueError('Unknown model entry')
        result = subprocess.run(argv, cwd=repo, env=env, capture_output=True, text=True, timeout=60)
        def read(name):
            p = base / name
            return [json.loads(x) for x in p.read_text().splitlines()] if p.exists() else []
        return dict(exit=result.returncode, stdout=result.stdout, stderr=result.stderr,
                    checker=read('checker.jsonl'), lake=read('lake.jsonl'),
                    intercepted=[p.name for p in base.glob('intercepted-*')],
                    startup_ran=(base / 'startup-ran').exists())

class Adversarial(unittest.TestCase):
    def success(self, result, rows):
        self.assertEqual(result['exit'], 0, result['stderr'])
        self.assertEqual([x['argv'] for x in result['checker']], [['-v', r['module']] for r in rows])
        self.assertEqual(result['stdout'], ''.join('replaying ' + r['module'] + '\n' for r in rows))
        self.assertEqual(len(result['lake']), 1)
        self.assertEqual(result['intercepted'], [])
        self.assertFalse(result['startup_ran'])
        self.assertEqual(len({x['pid'] for x in result['checker']}), len(rows))
        self.assertIn('-p', result['lake'][0]['argv'])
        for row in result['checker']:
            self.assertEqual(row['cwd'], 'repo')
            self.assertEqual(row['uid'], row['euid'])
            self.assertEqual(row['environment'], dict(LEAN_PATH='/model/objects with spaces:/model/packages',
                LEAN_SRC_PATH='/model/source', LEAN_SYSROOT='/model/toolchain', LEAN_NUM_THREADS='1',
                LEAN_STACK_SIZE_KB='65536', MIMALLOC_ARENA_RESERVE='128MiB', LANG='C.UTF-8', LC_ALL='C.UTF-8',
                MODEL_SENTINEL='set by fake Lake'))

    def test_all_567_with_all_initial_and_after_lake_functions(self):
        self.success(model(ROWS, imported=NAMES, after=NAMES, forged_shelopts=True), ROWS)

    def test_each_invoked_primitive_is_not_intercepted(self):
        for name in NAMES:
            with self.subTest(name=name):
                self.success(model(SMALL, imported=[name], after=[name]), SMALL)

    def test_direct_privileged_shebang(self):
        self.success(model(SMALL, imported=NAMES, after=NAMES, entry='shebang'), SMALL)

    def test_missing_checker_and_imported_not_found_handler(self):
        for location in ['initial', 'after']:
            with self.subTest(location=location):
                r = model(SMALL, imported=NAMES if location == 'initial' else [],
                          after=NAMES if location == 'after' else [], missing=True)
                self.assertEqual(r['exit'], 127)
                self.assertEqual(r['checker'], [])
                self.assertEqual(r['intercepted'], [])

    def test_nonexecutable_checker_and_imported_not_found_handler(self):
        r = model(SMALL, imported=NAMES, after=NAMES, nonexec=True)
        self.assertEqual(r['exit'], 126)
        self.assertEqual(r['checker'], [])
        self.assertEqual(r['intercepted'], [])

    def test_37_126_127_and_signals_stop_without_successors(self):
        for code, sig, expected in [(37, None, 37), (126, None, 126), (127, None, 127),
                                    (None, signal.SIGTERM, 143), (None, signal.SIGKILL, 137)]:
            with self.subTest(code=code, signal=sig):
                r = model(SMALL, imported=NAMES, after=NAMES, exit_code=code, sig=sig)
                self.assertEqual(r['exit'], expected, r['stderr'])
                self.assertEqual([x['argv'][1] for x in r['checker']], [x['module'] for x in SMALL[:8]])
                self.assertEqual(r['intercepted'], [])

    def test_first_and_last_failures(self):
        for index in [0, len(SMALL) - 1]:
            with self.subTest(index=index):
                r = model(SMALL, imported=NAMES, after=NAMES, exit_code=37, fail_index=index)
                self.assertEqual(r['exit'], 37)
                self.assertEqual(len(r['checker']), index + 1)

    def test_lake_failure_is_propagated(self):
        r = model(SMALL, imported=NAMES, lake_fail=True)
        self.assertEqual(r['exit'], 53)
        self.assertEqual(r['checker'], [])

    def test_startup_hooks_are_not_executed_and_are_rejected(self):
        for key in ['BASH_ENV', 'ENV']:
            with self.subTest(key=key):
                r = model(SMALL, imported=NAMES, hook=key)
                self.assertEqual(r['exit'], 2)
                self.assertFalse(r['startup_ran'])
                self.assertEqual(r['intercepted'], [])
                self.assertEqual(r['lake'], [])
                self.assertEqual(r['checker'], [])

    def test_after_lake_startup_hook_is_not_executed(self):
        self.success(model(SMALL, imported=NAMES, after=NAMES, after_hook=True), SMALL)

    def test_unprivileged_mode_has_no_loop_even_with_exit_function(self):
        r = model(SMALL, imported=['exec', 'command', 'hash', 'exit', 'false'], entry='unprivileged')
        self.assertEqual(r['exit'], 1)
        self.assertEqual(r['checker'], [])
        self.assertEqual(r['lake'], [])
        self.assertEqual(r['intercepted'], [])

    def test_unprivileged_or_late_mode_templates_are_never_accepted(self):
        self.assertTrue(valid_contract(SHELL, RUN))
        for shell, run in [(SHELL.replace(' -p ', ' '), RUN), (SHELL, RUN.replace(' -p ', ' ')),
                           ('bash {0}', 'set -p; ' + RUN), (SHELL, 'bash scripts/KernelCheck.sh')]:
            self.assertFalse(valid_contract(shell, run))

    def test_v1_false_success_controls_are_detected(self):
        for name in ['exec', 'command']:
            with self.subTest(name=name):
                r = model(SMALL, imported=[name], script=V1, entry='unprivileged')
                self.assertEqual(r['exit'], 0)
                self.assertEqual(r['checker'], [])
                self.assertTrue(r['intercepted'])

    def test_v1_missing_command_handler_false_success_control(self):
        r = model(SMALL, imported=['command_not_found_handle'], missing=True, script=V1, entry='unprivileged')
        self.assertEqual(r['exit'], 0)
        self.assertEqual(r['checker'], [])
        self.assertTrue(r['intercepted'])

    def test_mode_flag_alone_does_not_prove_privileged_startup(self):
        # Demonstrate why trusted runner argv, not just `case $-`, is mandatory.
        r = model(SMALL, imported=['exec'], script=NEW, entry='unprivileged', forged_shelopts=True)
        self.assertEqual(r['exit'], 0)
        self.assertEqual(r['checker'], [])
        self.assertTrue(r['intercepted'])
        self.assertFalse(valid_contract(SHELL.replace(' -p ', ' '), RUN))

    def test_syntax_only(self):
        r = subprocess.run(['/bin/bash', '-n', str(HERE / 'PROPOSED-KernelCheck.sh')], capture_output=True)
        self.assertEqual(r.returncode, 0, r.stderr)

if __name__ == '__main__':
    unittest.main(verbosity=2)
