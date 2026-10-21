"""Actual control-function models; native processes/resources/leases blocked."""
from pathlib import Path
import contextlib
import copy
import fcntl
import hashlib
import importlib.util
import json
import os
import resource
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCHEDULE = ROOT / 'checkpoints/light-eft-sequential-validation-schedule-20261021'
spec = importlib.util.spec_from_file_location('_integration_exact_controls', SCHEDULE / 'workflow_identity.py')
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)
SCRIPT = (ROOT / 'scripts/KernelCheck.sh').read_bytes()
WORKFLOW = (ROOT / '.github/workflows/lean.yml').read_bytes()

def forbidden(*a, **kw):
    raise AssertionError('Source-only control tests cannot spawn/admit/claim')

class Controls(unittest.TestCase):
    def setUp(self):
        stack = contextlib.ExitStack()
        self.addCleanup(stack.close)
        for owner, name in [(subprocess, 'Popen'), (fcntl, 'flock'), (resource, 'setrlimit'),
                            (os, 'fork'), (os, 'killpg'), (os, 'waitid'), (os, 'wait4'), (os, 'waitpid')]:
            stack.enter_context(patch.object(owner, name, side_effect=forbidden))

    def test_reviewed_pair_is_accepted(self):
        controls.replay_launch_controls(SCRIPT, WORKFLOW)

    def test_each_script_startup_flag_and_primitives_are_hash_pinned(self):
        for before, after in [(b'#!/bin/bash -p', b'#!/bin/bash'),
                              (b'/bin/bash --noprofile --norc -p -euo', b'/bin/bash --noprofile --norc -euo'),
                              (b'    exec lake env', b'    exec true # lake env'),
                              (b'    command leanchecker', b'    command true # leanchecker'),
                              (b'    hash -r', b'    : # hash -r')]:
            with self.subTest(before=before):
                self.assertIn(before, SCRIPT)
                with self.assertRaises(ValueError):
                    controls.replay_launch_controls(SCRIPT.replace(before, after), WORKFLOW)

    def test_each_workflow_entry_flag_is_required(self):
        for before, after in [(b'shell: /bin/bash --noprofile --norc -p -e', b'shell: /bin/bash --noprofile --norc -e'),
                              (b'run: /bin/bash --noprofile --norc -p -e', b'run: /bin/bash --noprofile --norc -e'),
                              (b'shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}', b'shell: bash'),
                              (b'run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh', b'run: bash scripts/KernelCheck.sh')]:
            with self.subTest(before=before):
                self.assertIn(before, WORKFLOW)
                with self.assertRaises(ValueError):
                    controls.replay_launch_controls(SCRIPT, WORKFLOW.replace(before, after))

    def test_duplicate_global_step_is_rejected(self):
        with self.assertRaises(ValueError):
            controls.replay_launch_controls(SCRIPT, WORKFLOW + b'      - name: Replay every project module through the Lean kernel\n')

    def fixture(self, mutation=None):
        with tempfile.TemporaryDirectory(prefix='light-eft-controls-', dir='/tmp') as tmp:
            root = Path(tmp)
            schedule = root / 'checkpoints/light-eft-sequential-validation-schedule-20261021'
            paths = ['.github/workflows/lean.yml', '.github/workflows/light-eft-fair-bit-focused.yml',
                     'scripts/KernelCheck.sh', 'checkpoints/light-eft-sequential-validation-schedule-20261021/workflow_identity.py',
                     'checkpoints/light-eft-sequential-validation-schedule-20261021/acceptance.py',
                     'checkpoints/light-eft-canonical-output-adapter-20261020/ci_policy.py']
            frozen = {}
            for rel in paths:
                data = SCRIPT if rel == 'scripts/KernelCheck.sh' else WORKFLOW if rel == '.github/workflows/lean.yml' else b'MODEL bound control\n'
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(data)
                frozen[p] = data
            rows = [dict(path=rel, bytes=len(frozen[root / rel]), sha256=hashlib.sha256(frozen[root / rel]).hexdigest()) for rel in paths]
            sp = root / 'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci-spec.json'
            sp.parent.mkdir(parents=True, exist_ok=True)
            if mutation == 'missing_row':
                rows = [r for r in rows if r['path'] != 'scripts/KernelCheck.sh']
            if mutation in ['script_drift', 'coordinated_bad_script']:
                p = root / 'scripts/KernelCheck.sh'
                data = SCRIPT.replace(b'command leanchecker', b'command true # leanchecker')
                p.write_bytes(data)
                if mutation == 'coordinated_bad_script':
                    frozen[p] = data
                    rows = [dict(path=r['path'], bytes=len(data), sha256=hashlib.sha256(data).hexdigest()) if r['path'] == 'scripts/KernelCheck.sh' else r for r in rows]
            if mutation == 'coordinated_bad_workflow':
                p = root / '.github/workflows/lean.yml'
                data = WORKFLOW.replace(b'shell: /bin/bash --noprofile --norc -p -e', b'shell: /bin/bash --noprofile --norc -e')
                p.write_bytes(data)
                frozen[p] = data
                rows = [dict(path=r['path'], bytes=len(data), sha256=hashlib.sha256(data).hexdigest()) if r['path'] == '.github/workflows/lean.yml' else r for r in rows]
            sp.write_text(json.dumps(dict(engine_files=rows)))
            frozen[sp] = sp.read_bytes()
            if mutation == 'stale_spec':
                frozen[sp] = b'OLD Git specification'
            if mutation == 'symlink_script':
                p = root / 'scripts/KernelCheck.sh'
                q = root / 'real-model-script'
                p.rename(q)
                p.symlink_to(q)
            with patch.object(controls, 'ROOT', root), patch.object(controls, 'HERE', schedule), \
                 patch.object(controls, 'SPEC', sp), patch.object(controls, 'git_bytes', side_effect=lambda p: frozen[p]):
                return controls.exact_controls()

    def test_real_exact_controls_checks_and_returns_script_binding(self):
        rows = self.fixture()
        self.assertEqual(len(rows), 6)
        self.assertEqual(rows['scripts/KernelCheck.sh']['sha256'], hashlib.sha256(SCRIPT).hexdigest())

    def test_missing_stale_drift_and_symlink_bindings_are_rejected(self):
        for mutation in ['missing_row', 'stale_spec', 'script_drift', 'symlink_script']:
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.fixture(mutation)

    def test_matching_metadata_and_git_cannot_weaken_reviewed_pair(self):
        for mutation in ['coordinated_bad_script', 'coordinated_bad_workflow']:
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.fixture(mutation)

if __name__ == '__main__':
    unittest.main(verbosity=2)
