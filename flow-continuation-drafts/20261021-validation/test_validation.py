"""Source-only parser/selection regressions. Never invokes Lean or CI."""
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
import tempfile
import json

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('flow_validation', Path(__file__).with_name('validate.py'))
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)


class ValidationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.base, cls.new, cls.sources, cls.order, _ = v.plan()

    def inventory(self):
        # Synthetic parser input only; never represented as a Lean audit receipt.
        owners = {n + '.example': n for n in self.sources}
        owners.update({n: 'DirectedFlowCutGap.OriginalStoreCorrectness' for n in v.REQUIRED})
        roots = [(owner, name) for name, owner in owners.items() if owner in self.new]
        lines = ['MODULE ' + n for n in sorted(self.sources)]
        lines += ['ATTR ' + owner + '|' + name for name, owner in owners.items()]
        lines += ['ROOT ' + owner + '|' + name for owner, name in roots]
        lines += [f'AUDIT_PASS modules=737 declarations={len(owners)} roots={len(roots)} closure=1000']
        return '\n'.join(lines) + '\n', owners

    def test_union_and_import_order(self):
        self.assertEqual((len(self.base), len(self.new), len(self.order)), (722, 15, 737))
        position = {name: i for i, name in enumerate(self.order)}
        for name, data in self.sources.items():
            for dep in v.imports(data):
                self.assertLess(position[dep], position[name])

    def test_generated_imports_precede_definitions(self):
        for selected, new in [(self.base, set()), (set(self.sources), self.new)]:
            lines = v.audit_source(selected, new).splitlines()
            self.assertEqual(sum(l.startswith('import DirectedFlowCutGap.') for l in lines), len(selected))
            first_def = next(i for i, l in enumerate(lines) if l.startswith('def '))
            self.assertFalse(any(l.startswith('import ') for l in lines[first_def:]))

    def test_complete_inventory(self):
        text, owners = self.inventory()
        self.assertEqual(v.parse_audit(text, set(self.sources), self.new), owners)

    def test_wrong_module_with_same_count_rejected(self):
        text, _ = self.inventory()
        text = text.replace('MODULE DirectedFlowCutGap.OriginalStoreInitial\n',
                            'MODULE DirectedFlowCutGap.NotTheOriginalStore\n')
        with self.assertRaises(RuntimeError):
            v.parse_audit(text, set(self.sources), self.new)

    def test_missing_or_duplicate_new_root_rejected(self):
        text, _ = self.inventory()
        root = next(l + '\n' for l in text.splitlines() if l.startswith('ROOT '))
        for bad in [text.replace(root, ''), text + root]:
            with self.assertRaises(RuntimeError):
                v.parse_audit(bad, set(self.sources), self.new)

    def test_missing_correctness_root_rejected(self):
        text, _ = self.inventory()
        name = v.REQUIRED[0]
        # Remove both ownership and root lines and adjust counts: explicit required
        # presence must still reject the forged complete-looking evidence.
        owner = 'DirectedFlowCutGap.OriginalStoreCorrectness'
        text = text.replace('ATTR ' + owner + '|' + name + '\n', '')
        text = text.replace('ROOT ' + owner + '|' + name + '\n', '')
        text = text.replace('declarations=741 roots=19', 'declarations=740 roots=18')
        with self.assertRaises(RuntimeError):
            v.parse_audit(text, set(self.sources), self.new)

    def test_missing_success_rejected(self):
        text, _ = self.inventory()
        with self.assertRaises(RuntimeError):
            v.parse_audit(text.replace('AUDIT_PASS', 'INCOMPLETE'), set(self.sources), self.new)

    def test_physical_fixture_is_executed_and_requires_all_cases(self):
        self.assertEqual(v.fixture_arguments('degenerate', Path('fixture.lean'), 10),
                         ['--run', 'fixture.lean', 'all'])
        with self.assertRaises(RuntimeError):
            v.fixture_pass('degenerate', '')
        cases = ['empty', 'one-zero-no-demands', 'self-demand', 'two-unit-direct']
        text = ''.join('PASS final dispatcher physical degenerate ' + n + ' instructions=1\n' for n in cases)
        v.fixture_pass('degenerate', text)
        with self.assertRaises(RuntimeError):
            v.fixture_pass('positive-physical', 'NATURAL_DIAGNOSTIC_MATCH_ONLY orderedStates=9 x\n')

    def test_early_failure_receipt_without_any_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / 'fresh-output'
            argv = ['validate.py', '--execute', '--output', str(out)]
            with patch.object(sys, 'argv', argv), patch.object(v, 'plan', side_effect=RuntimeError('synthetic preflight failure')):
                with self.assertRaisesRegex(RuntimeError, 'synthetic preflight'):
                    v.main()
            report = json.loads((out / 'receipt.json').read_text())
            self.assertEqual(report['status'], 'failed_preflight')
            self.assertEqual(report['compiled'], [])
            self.assertFalse(report['acceptance'])
            self.assertTrue((out / 'SHA256SUMS').exists())

    def identity_case(self, mutation=None, initial_status='gates_passed_pending_independent_review'):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            here = root / 'validation'
            here.mkdir()
            (here / 'validate.py').write_text('original validator bytes')
            workflow = root / '.github/workflows/flow-737-validation.yml'
            workflow.parent.mkdir(parents=True)
            workflow.write_text('original workflow bytes')
            output = root / 'output'
            src = output / 'src/DirectedFlowCutGap/A.lean'
            src.parent.mkdir(parents=True)
            source = {'DirectedFlowCutGap.A': b'original Lean source'}
            src.write_bytes(source['DirectedFlowCutGap.A'])
            expected = 'a' * 40
            current = expected
            with patch.object(v, 'HERE', here), patch.object(v, 'REPO', root):
                report = {'status': initial_status, 'validator_bindings': v.validator_snapshot(),
                          'commit': expected, 'acceptance': False}
                if mutation == 'head':
                    current = 'b' * 40
                elif mutation == 'validator':
                    (here / 'validate.py').write_text('changed validator bytes')
                elif mutation == 'added-validator':
                    (here / 'extra.py').write_text('new file')
                elif mutation == 'workflow':
                    workflow.write_text('changed workflow bytes')
                elif mutation == 'overlay':
                    src.write_bytes(b'changed Lean source')
                elif mutation == 'extra-overlay':
                    (src.parent / 'Extra.lean').write_text('new source')
                def clean_git(*args):
                    if args == ('rev-parse', 'HEAD'):
                        return (current + '\n').encode()
                    if args[0] == 'status':
                        return b''  # A clean switch must still be rejected.
                    raise AssertionError(args)
                with patch.object(v, 'git', side_effect=clean_git):
                    passed = v.postflight_identity(report, expected, source, output)
                return passed, report

    def test_unchanged_postflight_identity(self):
        passed, report = self.identity_case()
        self.assertTrue(passed)
        self.assertEqual(report['status'], 'gates_passed_pending_independent_review')

    def test_clean_changed_head_cannot_pass(self):
        passed, report = self.identity_case('head')
        self.assertFalse(passed)
        self.assertFalse(report['head_postflight_passed'])
        self.assertEqual(report['status'], 'failed')

    def test_changed_validator_set_or_bytes_cannot_pass(self):
        for mutation in ['validator', 'added-validator', 'workflow']:
            with self.subTest(mutation=mutation):
                passed, report = self.identity_case(mutation)
                self.assertFalse(passed)
                self.assertFalse(report['validator_postflight_passed'])
                self.assertEqual(report['status'], 'failed')

    def test_changed_overlay_set_or_bytes_cannot_pass(self):
        for mutation in ['overlay', 'extra-overlay']:
            with self.subTest(mutation=mutation):
                passed, report = self.identity_case(mutation)
                self.assertFalse(passed)
                self.assertFalse(report['overlay_postflight_passed'])
                self.assertEqual(report['status'], 'failed')

    def test_failed_attempt_still_checks_identity_and_is_never_promoted(self):
        passed, report = self.identity_case('head', initial_status='failed')
        self.assertFalse(passed)
        self.assertFalse(report['head_postflight_passed'])
        self.assertEqual(report['status'], 'failed')
        passed, report = self.identity_case(initial_status='failed')
        self.assertTrue(passed)
        self.assertEqual(report['status'], 'failed')


if __name__ == '__main__':
    unittest.main()
