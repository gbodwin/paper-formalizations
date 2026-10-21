"""Synthetic runner/state models. Every process, exec, lease and timer action blocked."""
from pathlib import Path
import contextlib
import copy
import fcntl
import importlib.util
import json
import os
import resource
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
s = importlib.util.spec_from_file_location('_candidate_replay_admission', HERE / 'replay_preflight.py')
api = importlib.util.module_from_spec(s);s.loader.exec_module(api)
RAW_BINDING = api.binding
BODY = (HERE / 'PROPOSED-KernelCheck.sh').read_text().split("-c '\n", 1)[1].split("'\n    ;;", 1)[0]
ARGV = ['/bin/bash', '--noprofile', '--norc', '-p', '-euo', 'pipefail', '-c', BODY]
IDS = dict(uid=12, euid=12, gid=34, egid=34)
ENV = dict(GITHUB_RUN_ID='1', GITHUB_RUN_ATTEMPT='1', LEAN_NUM_THREADS='1', LANG='C.UTF-8', PATH='/fake/bin')

def forbidden(*a, **kw):
    raise AssertionError('Candidate admission must not execute on the worker')

class Handoff(RuntimeError):
    pass

class Models(unittest.TestCase):
    def setUp(self):
        self.stack = contextlib.ExitStack();self.addCleanup(self.stack.close)
        for owner, name in [(subprocess, 'Popen'), (os, 'fork'), (os, 'execv'), (os, 'killpg'),
                            (fcntl, 'flock'), (resource, 'setrlimit'), (signal, 'setitimer'), (signal, 'signal')]:
            self.stack.enter_context(patch.object(owner, name, side_effect=forbidden))

    @contextlib.contextmanager
    def fixture(self):
        with tempfile.TemporaryDirectory(prefix='light-eft-admission-model-', dir='/tmp') as temp, contextlib.ExitStack() as stack:
            self.env = dict(ENV, RUNNER_TEMP=temp)
            self.ci = dict(job='MODEL full', host='MODEL runner A', source='a' * 40)
            self.platform_state = dict(ids=IDS, bash='MODEL Bash', python='MODEL Python', sources='MODEL source bindings')
            self.carrier = 'MODEL installed carrier'
            def bind(p):
                p = Path(p)
                data = p.read_bytes() if p.is_file() else self.carrier.encode()
                return dict(path=str(p), canonical=str(p.resolve()), sha256=api.sha(data), identity=[1, 2, len(data), api.sha(data)])
            def platform(env):
                api.normal(env, IDS)
                return copy.deepcopy(self.platform_state)
            self.timer = stack.enter_context(patch.object(api.signal, 'setitimer'))
            self.exec = stack.enter_context(patch.object(api.os, 'execv', side_effect=Handoff))
            stack.enter_context(patch.object(api, 'context', side_effect=lambda env: copy.deepcopy(self.ci)))
            stack.enter_context(patch.object(api, 'platform', side_effect=platform))
            stack.enter_context(patch.object(api, 'binding', side_effect=bind))
            stack.enter_context(patch.object(api.shutil, 'which', return_value='/fake/lake'))
            stack.enter_context(patch.object(api, 'observe_lake', side_effect=lambda env: dict(environment=api.projection(env), checker='MODEL pinned checker', tools='MODEL pinned tools')))
            yield

    def boot(self):
        api.bootstrap(self.env)

    def before(self):
        with self.assertRaises(Handoff):api.before_lake(self.env, ARGV)

    def enter(self):
        self.lake_env = dict(self.env, PATH='/fake/tool/bin:/fake/bin', LEAN_PATH='/objects', LEAN_SRC_PATH='/source',
                             LEAN_SYSROOT='/fake/tool', LD_LIBRARY_PATH='/fake/lib')
        with self.assertRaises(Handoff):api.enter(self.lake_env, ARGV)

    def test_normal_exports_and_equal_uid_gid(self):
        api.normal(ENV, IDS)
        for name in api.ABSENT:
            for value in ['', 'normal-looking', 'hostile']:
                with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                    api.normal(dict(ENV, **{name: value}), IDS)
        for key in ['euid', 'egid']:
            with self.subTest(key=key), self.assertRaises(ValueError):api.normal(ENV, dict(IDS, **{key: 999}))

    def test_each_projection_field_and_absent_empty_differ(self):
        baseline = dict(environment=api.projection(ENV), checker='pinned', tools='pinned')
        api.equivalent(baseline, copy.deepcopy(baseline))
        for key in api.PROJECTIONS:
            changed = copy.deepcopy(baseline);changed['environment'][key] = 'other'
            with self.subTest(key=key), self.assertRaises(ValueError):api.equivalent(baseline, changed)
        x = copy.deepcopy(baseline);x['environment']['LEAN_PATH'] = ''
        with self.assertRaises(ValueError):api.equivalent(baseline, x)
        for key in ['checker', 'tools']:
            x = copy.deepcopy(baseline);x[key] = 'different'
            with self.assertRaises(ValueError):api.equivalent(baseline, x)

    def test_only_pinned_inner_argv_and_loop_are_accepted(self):
        api.command(ARGV)
        for mutation in [ARGV[:-1], [*ARGV[:3], '+p', *ARGV[4:]], [*ARGV[:-1], BODY + '\ntrue']]:
            with self.assertRaises(ValueError):api.command(mutation)

    def test_complete_four_phase_model_and_cancelled_handoff_timers(self):
        with self.fixture():
            self.boot();self.before();self.enter();api.verify(self.lake_env, 'ehpuBc', '5.2.37(1)-release')
            root = api.root(self.env)
            self.assertEqual({p.name for p in root.iterdir()}, {'bootstrap.json', 'before-lake.json', 'lake-baseline.json', 'verified.json'})
            self.assertEqual(self.exec.call_count, 2)
            self.assertEqual(self.exec.call_args_list[0].args[0], '/fake/lake')
            self.assertEqual(self.exec.call_args_list[1].args, ('/bin/bash', ARGV))
            self.assertEqual(self.timer.call_args_list, [unittest.mock.call(signal.ITIMER_REAL, 0), unittest.mock.call(signal.ITIMER_REAL, 0)])

    def test_missing_boot_or_phase_never_hands_off(self):
        with self.fixture():
            with self.assertRaises(FileNotFoundError):api.before_lake(self.env, ARGV)
            self.boot()
            with self.assertRaises(FileNotFoundError):api.enter(self.env, ARGV)
            with self.assertRaises(FileNotFoundError):api.verify(self.env, 'p', '5.2')
            self.exec.assert_not_called()

    def test_host_platform_or_source_drift_stops_before_lake(self):
        for field in ['host', 'source', 'platform']:
            with self.subTest(field=field), self.fixture():
                self.boot()
                if field == 'platform':self.platform_state['sources'] = 'changed'
                else:self.ci[field] = 'changed'
                with self.assertRaises(ValueError):api.before_lake(self.env, ARGV)
                self.exec.assert_not_called()

    def test_inherited_environment_or_carrier_drift_stops(self):
        with self.fixture():
            self.boot()
            with self.assertRaises(ValueError):api.before_lake(dict(self.env, PATH='/other'), ARGV)
            self.carrier = 'changed'
            with self.assertRaises(ValueError):api.before_lake(self.env, ARGV)
            self.exec.assert_not_called()

    def test_baseline_mismatch_or_bad_shell_never_verifies(self):
        with self.fixture():
            self.boot();self.before();self.enter()
            for key in api.PROJECTIONS:
                with self.subTest(key=key), self.assertRaises(ValueError):api.verify(dict(self.lake_env, **{key: 'different'}), 'p', '5.2')
            for flags, version in [('', '5.2'), ('p', 'not-admitted')]:
                with self.assertRaises(ValueError):api.verify(self.lake_env, flags, version)
            self.assertFalse((api.root(self.env) / 'verified.json').exists())

    def test_duplicate_records_and_unsafe_record_fail(self):
        with self.fixture():
            self.boot()
            with self.assertRaises(FileExistsError):api.bootstrap(self.env)
            self.before()
            with self.assertRaises(FileExistsError):api.before_lake(self.env, ARGV)
            p = api.root(self.env) / 'before-lake.json';copy_path = p.with_name('linked-data');p.rename(copy_path);p.symlink_to(copy_path)
            with self.assertRaises(ValueError):api.enter(self.env, ARGV)

    def test_unbound_current_proposal_is_not_admission(self):
        with tempfile.TemporaryDirectory(dir='/tmp') as temp:
            root = Path(temp)
            critical = ['helper.py', 'scripts/KernelCheck.sh', '.github/workflows/lean.yml', 'lakefile.toml', 'lean-toolchain', 'lake-manifest.json']
            files = {}
            for rel in critical:
                p = root / rel;p.parent.mkdir(parents=True, exist_ok=True);p.write_bytes(b'MODEL source');files[rel] = p.read_bytes()
            for name in api.SPECS:
                rel = 'checkpoints/' + name + '/ci-spec.json';p = root / rel;p.parent.mkdir(parents=True, exist_ok=True);p.write_text('{"engine_files": []}');files[rel] = p.read_bytes()
            with patch.object(api, 'ROOT', root), patch.object(api, 'REL', 'helper.py'), \
                 patch.object(api, 'SCRIPT_SHA', api.sha(b'MODEL source')), patch.object(api, 'git', side_effect=lambda *args: files[args[-1][5:]]):
                with self.assertRaisesRegex(ValueError, 'not bound'):api.checked_sources()

    def test_observed_tool_hash_shadow_and_missing_checker_refuse(self):
        with tempfile.TemporaryDirectory(dir='/tmp') as temp:
            root = Path(temp);tool = root / 'tool';(tool / 'bin').mkdir(parents=True)
            for name in ['lean', 'leanchecker', 'lake']:(tool / 'bin' / name).write_bytes(name.encode())
            p = root / 'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci-spec.json';p.parent.mkdir(parents=True)
            p.write_text(json.dumps(dict(toolchain='leanprover/lean4:v4.34.0', tool_hashes={n: api.sha(n.encode()) for n in ['lean', 'leanchecker']})))
            env = dict(ENV, LEAN_SYSROOT=str(tool), LAKE=str(tool / 'bin/lake'))
            with patch.object(api, 'ROOT', root), patch.object(api.shutil, 'which', return_value=str(tool / 'bin/leanchecker')):
                api.observe_lake(env)
                (tool / 'bin/leanchecker').write_bytes(b'changed')
                with self.assertRaises(ValueError):api.observe_lake(env)
                (tool / 'bin/leanchecker').write_bytes(b'leanchecker')
            with patch.object(api, 'ROOT', root), patch.object(api.shutil, 'which', return_value=None):
                with self.assertRaises(ValueError):api.observe_lake(env)
            shadow = root / 'other';shadow.write_bytes(b'leanchecker')
            with patch.object(api, 'ROOT', root), patch.object(api.shutil, 'which', return_value=str(shadow)):
                with self.assertRaises(ValueError):api.observe_lake(env)

    def test_timeout_stays_failure_and_is_recorded_without_handoff(self):
        with self.fixture():
            self.boot()
            with patch.dict(os.environ, self.env, clear=True), patch.object(sys, 'argv', ['helper', 'bootstrap']), \
                 patch.object(api.signal, 'getitimer', return_value=(0.0, 0.0)), patch.object(api.signal, 'signal'), \
                 patch.object(api, 'bootstrap', side_effect=TimeoutError('MODEL90second deadline')):
                with self.assertRaises(TimeoutError):api.main()
            self.exec.assert_not_called()
            self.assertIn('TimeoutError', (api.root(self.env) / 'failure-bootstrap.json').read_text())

if __name__ == '__main__':
    unittest.main(verbosity=2)
