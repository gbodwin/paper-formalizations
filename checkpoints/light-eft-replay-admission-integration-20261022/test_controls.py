"""Synthetic exact-control models; process, exec, admission, lease and timers blocked."""
from pathlib import Path
import contextlib
import fcntl
import hashlib
import importlib.util
import json
import os
import resource
import signal
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCHEDULE = ROOT / 'checkpoints/light-eft-sequential-validation-schedule-20261021'
HELPER_PATH = 'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py'
s = importlib.util.spec_from_file_location('_integrated_replay_controls', SCHEDULE / 'workflow_identity.py')
controls = importlib.util.module_from_spec(s);s.loader.exec_module(controls)
SCRIPT = (ROOT / 'scripts/KernelCheck.sh').read_bytes()
WORKFLOW = (ROOT / '.github/workflows/lean.yml').read_bytes()
HELPER = (ROOT / HELPER_PATH).read_bytes()
BOOT = b'      - name: Observe replay launcher admission on this runner\n'
GLOBAL = b'      - name: Replay every project module through the Lean kernel\n'
UPLOAD = b'      - name: Preserve complete staged-gate evidence including failures\n'
EVIDENCE = b'            ${{ runner.temp }}/light-eft-replay-admission-${{ github.run_id }}-${{ github.run_attempt }}\n'

def forbidden(*a, **kw):
    raise AssertionError('Source-only models cannot execute admission/native work')

def in_region(data, start, end, old, new):
    a = data.index(start);b = data.index(end, a)
    assert old in data[a:b]
    return data[:a] + data[a:b].replace(old, new) + data[b:]

class Controls(unittest.TestCase):
    def setUp(self):
        stack = contextlib.ExitStack();self.addCleanup(stack.close)
        for owner, name in [(subprocess, 'Popen'), (os, 'fork'), (os, 'execv'), (os, 'killpg'),
                            (os, 'waitid'), (os, 'wait4'), (os, 'waitpid'), (fcntl, 'flock'),
                            (resource, 'setrlimit'), (signal, 'setitimer'), (signal, 'signal')]:
            stack.enter_context(patch.object(owner, name, side_effect=forbidden))

    def accepts(self, script=SCRIPT, workflow=WORKFLOW, helper=HELPER):
        return controls.replay_launch_controls(script, workflow, helper)

    def test_exact_reviewed_triplet_and_mutual_loop_pins(self):
        self.accepts()
        loop = SCRIPT.split(b"-c '\n", 1)[1].split(b"'\n    ;;", 1)[0]
        for line in [b"SCRIPT_SHA = '" + hashlib.sha256(SCRIPT).hexdigest().encode() + b"'\n",
                     b"LOOP_SHA = '" + hashlib.sha256(loop).hexdigest().encode() + b"'\n"]:
            self.assertEqual(HELPER.count(line), 1)

    def test_helper_content_and_handoff_timers_are_pinned(self):
        for before, after in [(b'signal.setitimer(signal.ITIMER_REAL, 0)', b'signal.setitimer(signal.ITIMER_REAL, 90)'),
                              (b"'lake-baseline.json'", b"'unverified-baseline.json'"),
                              (b"'p' in flags", b'True')]:
            with self.subTest(before=before):
                self.assertIn(before, HELPER)
                with self.assertRaises(ValueError):self.accepts(helper=HELPER.replace(before, after))
        with self.assertRaises(TypeError):controls.replay_launch_controls(SCRIPT, WORKFLOW)

    def test_script_privileged_handoff_and_before_first_checker_are_pinned(self):
        for before, after in [(b'#!/bin/bash -p', b'#!/bin/bash'),
                              (b'before-lake /bin/bash --noprofile --norc -p', b'before-lake /bin/bash --noprofile --norc'),
                              (b' before-lake ', b' enter '),
                              (b' verify "$-" "$BASH_VERSION"', b' verify-forged p 5.2'),
                              (b'command leanchecker', b'command true # leanchecker')]:
            with self.subTest(before=before):
                self.assertIn(before, SCRIPT)
                with self.assertRaises(ValueError):self.accepts(script=SCRIPT.replace(before, after))

    def test_bootstrap_requires_isolated_absolute_python(self):
        for before, after in [(b'/usr/bin/python3 -I -B {0}', b'python3 {0}'),
                              (b"'bootstrap']", b"'verify']")]:
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.accepts(workflow=in_region(WORKFLOW, BOOT, GLOBAL, before, after))

    def test_same_job_metadata_required_on_both_steps(self):
        for start, end in [(BOOT, GLOBAL), (GLOBAL, b'      - name: Bind completed full validation')]:
            for key in [b'REF', b'SHA', b'PATH', b'REPOSITORY']:
                name = b'LIGHTEFT_JOB_WORKFLOW_' + key
                with self.subTest(start=start, key=key), self.assertRaises(ValueError):
                    self.accepts(workflow=in_region(WORKFLOW, start, end, name, b'UNBOUND_' + name))

    def test_missing_nonadjacent_duplicate_or_relocated_bootstrap_rejected(self):
        a, b = WORKFLOW.index(BOOT), WORKFLOW.index(GLOBAL)
        boot = WORKFLOW[a:b]
        cases = [WORKFLOW[:a] + WORKFLOW[b:],
                 WORKFLOW[:b] + b'      - name: Extra step\n        run: true\n' + WORKFLOW[b:],
                 WORKFLOW[:a] + boot + WORKFLOW[a:],
                 WORKFLOW[:a] + WORKFLOW[b:] + boot]
        for data in cases:
            with self.subTest(length=len(data)), self.assertRaises(ValueError):self.accepts(workflow=data)

    def test_outer_privileged_shell_and_script_entry_required(self):
        for before, after in [(b'shell: /bin/bash --noprofile --norc -p', b'shell: /bin/bash --noprofile --norc'),
                              (b'run: /bin/bash --noprofile --norc -p', b'run: /bin/bash --noprofile --norc')]:
            with self.subTest(before=before), self.assertRaises(ValueError):
                self.accepts(workflow=in_region(WORKFLOW, GLOBAL, b'      - name: Bind completed full validation', before, after))

    def test_evidence_must_be_in_the_existing_always_upload(self):
        cases = [WORKFLOW.replace(EVIDENCE, b''), WORKFLOW.replace(EVIDENCE, b'') + EVIDENCE,
                 WORKFLOW + EVIDENCE,
                 in_region(WORKFLOW, UPLOAD, b'  focused:\n', b'if: always()', b'if: success()')]
        for data in cases:
            with self.subTest(length=len(data)), self.assertRaises(ValueError):self.accepts(workflow=data)

    def fixture(self, mutation=None):
        with tempfile.TemporaryDirectory(prefix='light-eft-admission-controls-', dir='/tmp') as tmp:
            root = Path(tmp);schedule = root / 'checkpoints/light-eft-sequential-validation-schedule-20261021'
            paths = ['.github/workflows/lean.yml', '.github/workflows/light-eft-fair-bit-focused.yml',
                     'scripts/KernelCheck.sh', HELPER_PATH,
                     'checkpoints/light-eft-sequential-validation-schedule-20261021/workflow_identity.py',
                     'checkpoints/light-eft-sequential-validation-schedule-20261021/acceptance.py',
                     'checkpoints/light-eft-canonical-output-adapter-20261020/ci_policy.py']
            frozen = {}
            for rel in paths:
                data = {'.github/workflows/lean.yml': WORKFLOW, 'scripts/KernelCheck.sh': SCRIPT, HELPER_PATH: HELPER}.get(rel, b'MODEL control\n')
                p = root / rel;p.parent.mkdir(parents=True, exist_ok=True);p.write_bytes(data);frozen[p] = data
            def rows():
                return [dict(path=rel, bytes=len(frozen[root / rel]), sha256=hashlib.sha256(frozen[root / rel]).hexdigest()) for rel in paths]
            engine = rows()
            if mutation == 'missing_helper':engine = [r for r in engine if r['path'] != HELPER_PATH]
            if mutation in ['helper_drift', 'coordinated_helper']:
                p = root / HELPER_PATH;data = HELPER + b'\n# changed\n';p.write_bytes(data)
                if mutation == 'coordinated_helper':frozen[p] = data;engine = rows()
            if mutation == 'coordinated_script':
                p = root / 'scripts/KernelCheck.sh';data = SCRIPT.replace(b'command leanchecker', b'command true # leanchecker')
                p.write_bytes(data);frozen[p] = data;engine = rows()
            if mutation == 'coordinated_workflow':
                p = root / '.github/workflows/lean.yml';data = WORKFLOW.replace(EVIDENCE, b'')
                p.write_bytes(data);frozen[p] = data;engine = rows()
            spec = root / 'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci-spec.json'
            spec.parent.mkdir(parents=True, exist_ok=True);spec.write_text(json.dumps(dict(engine_files=engine)));frozen[spec] = spec.read_bytes()
            if mutation == 'stale_spec':frozen[spec] = b'old Git spec'
            if mutation == 'helper_symlink':
                p = root / HELPER_PATH;q = root / 'model-helper';p.rename(q);p.symlink_to(q)
            with patch.object(controls, 'ROOT', root), patch.object(controls, 'HERE', schedule), \
                 patch.object(controls, 'SPEC', spec), patch.object(controls, 'git_bytes', side_effect=lambda p: frozen[p]):
                return controls.exact_controls()

    def test_actual_exact_controls_returns_seven_bound_rows_including_helper(self):
        result = self.fixture()
        self.assertEqual(len(result), 7)
        self.assertEqual(result[HELPER_PATH]['sha256'], hashlib.sha256(HELPER).hexdigest())

    def test_missing_stale_drift_and_symlink_helper_fail_closed(self):
        for mutation in ['missing_helper', 'stale_spec', 'helper_drift', 'helper_symlink']:
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):self.fixture(mutation)

    def test_coordinated_metadata_and_git_cannot_weaken_triplet(self):
        for mutation in ['coordinated_helper', 'coordinated_script', 'coordinated_workflow']:
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):self.fixture(mutation)

if __name__ == '__main__':
    unittest.main(verbosity=2)
