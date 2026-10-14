#!/usr/bin/env python3
"""Source-only draft inventory. Does not invoke Lean, lake, or a test runtime."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
BASE = Path('/workspace/shared/flow-published722-recovered-20261014T0012Z/Improved Upper Bounds for the Directed Flow-Cut Gap')
DISPATCH = Path('/workspace/shared/flow-final-dispatch-reconstruction-20261014/DirectedFlowCutGap')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


lean_files = sorted(ROOT.glob('*.lean'))
assert len(lean_files) == 3
support = (ROOT / 'FinalDispatchPositiveFixtureSupport.lean').read_text()
physical = (ROOT / 'FinalDispatchPositivePhysicalSmoke.lean').read_text()
natural = (ROOT / 'FinalDispatchPositiveNaturalDiagnostic.lean').read_text()
for path in lean_files:
    text = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|extern|native_decide)\b', text), path
    assert '#eval' not in text and '#reduce' not in text, path
assert 'ImmutableReferenceTerminal.attempt FinalDispatch.program s' in physical
assert 'tickNatural' not in physical
assert 'BitState 13320' in physical
assert 'go remaining r.state next' in physical
assert 'go remaining r.state next' in natural
assert physical.count('attempts % 1000 == 0') == 2
assert natural.count('attempts % 1000 == 0') == 2
assert 't.successfulOperations+a.operations' in physical
assert 't.successfulOperations+actual.terminalOperations' in physical
assert 'actual.terminalOperations == 13336' in physical
assert 'BinaryFractionalGuesses.solveInput input' in support
assert 'decoded == some wanted' in physical
assert 'actual.state.heap.take start.heap.length == start.heap' in physical
assert 'checkOriginalRoots original finish' in physical
assert 'INCOMPLETE_PHYSICAL' in physical
assert 'NATURAL_DIAGNOSTIC_MATCH_ONLY' in natural
assert 'PASS_PHYSICAL' not in natural

# Static constructor count only, not an interpreter or high-level solver.
# A stored word of length L allocates one nil and L (flag,pair) pairs.
def word_cells(length):
    return 1 + 2 * length


def table_cells(length_pairs):
    return 1 + sum(word_cells(a) + word_cells(b) + 2 for a, b in length_pairs)


cost_cells = table_cells([(0, 1), (1, 1), (0, 1)])
matrix_cells = 1 + 3 * (word_cells(3) + 1)
demand_cells = table_cells([(0, 2)])
initial_cells = 1 + cost_cells + matrix_cells + demand_cells
assert initial_cells == 56
assert 2 * 1 + 2 * 3 .bit_length() + 3 == 9
assert 13320 + 16 == 13336

reference_paths = [BASE / 'DirectedFlowCutGap' / name for name in [
    'OriginalDispatchSpec.lean', 'BinaryFractionalDispatch.lean',
    'BinaryFractionalGuesses.lean', 'ImmutableReferenceSimulation.lean',
    'ImmutableReferenceTerminal.lean', 'PackedWordPairTable.lean',
    'GridFamilyEnvelope.lean', 'BinaryRational.lean',
]] + [BASE / 'verification' / name for name in [
    'GridFamilyInputSmoke.lean', 'GridFamilyInputNaturalSmoke.lean', 'OriginalDispatchSmoke.lean',
]] + sorted(DISPATCH.glob('*.lean'))
manifest = {
    'status': 'NEW_UNVERIFIED_UNRUN',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'checks': 'Python source inspection, token checks, hashes and static constructor arithmetic only',
    'lean_invoked': False,
    'compiler_invoked': False,
    'physical_runtime_invoked': False,
    'natural_runtime_invoked': False,
    'production_files_modified': False,
    'fixture': {
        'vertices': 3, 'edges': [[0, 1], [1, 2]], 'demands': [[0, 2]],
        'costs': [[0, 1], [1, 1], [0, 1]], 'initial_cells_static': initial_cells,
        'program_labels': 13320, 'entry': 13318, 'halt': 13319,
        'expected_terminal_charge_static': 13336, 'grid_entries_static': 9,
        'stop_tests_per_entry_static': 27, 'total_stop_tests_static': 243,
        'successful_instructions_measured': None, 'total_physical_charge_measured': None,
        'final_heap_measured': None, 'wall_seconds_measured': None, 'peak_rss_measured': None,
    },
    'draft_files': {path.name: {'sha256': digest(path), 'bytes': path.stat().st_size}
                    for path in sorted(ROOT.iterdir())
                    if path.is_file() and path.name != 'draft-manifest.json'},
    'inspected_source_snapshot_not_compilation_evidence': {
        str(path): digest(path) for path in reference_paths
    },
    'limitations': [
        'Lean parsing, elaboration, strict compilation and all runtime checks are unrun.',
        'Natural-reference diagnostics cannot count as a physical execution or paid-cost test.',
        'Source-tail recursion avoids explicit old-state return retention; native behavior is unmeasured.',
        'Physical sequential lookup/full-store copying and all retained output states remain unchanged.',
        'A passing fixture would not close parsing, all-input proof, kernel audit, CI or whole-paper gates.',
    ],
}
(ROOT / 'draft-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': manifest['status'], 'static_checks_passed': True,
                  'lean_sources': len(lean_files), 'initial_cells_static': initial_cells,
                  'manifest': str(ROOT / 'draft-manifest.json')}))
