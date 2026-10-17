"""Harmless synthetic boundary check of the production guard; no child process."""
from pathlib import Path
import datetime
import hashlib
import json
import batch_context
import child_runner

B = Path(__file__).resolve().parent


def main():
    gate = 4831838208
    batch = object.__new__(batch_context.Batch)
    first = {'module': 'LightEFTSpanners.BernoulliFlagEncoding', 'stage': 'compile'}
    assert batch.visible_gate(first) == gate
    assert batch.visible_gate({**first, 'stage': 'resolve'}) == 3221225472
    assert batch.visible_gate({**first, 'stage': 'replay'}) == 4294967296
    baseline = {'headroom': gate, 'nodes': [{'path': '/synthetic-boundary', 'limit': '17179869184',
        'oom': {'oom': 0}, 'pids_max': 'max', 'pids_current': 1, 'pids_events': {'max': 0}}]}
    cases = []
    for value, accepted in [(gate, True), (gate - 1, False)]:
        sample = {**baseline, 'headroom': value}
        error = None
        try:
            child_runner.check_memory(sample, baseline, batch.visible_gate(first))
            actual = True
        except child_runner.MemoryGuardError as exc:
            actual = False
            error = repr(exc)
        assert actual == accepted
        cases.append({'visible_bytes': value, 'expected_accepted': accepted, 'actual_accepted': actual, 'error': error})
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Synthetic equality/one-byte-below test of actual production visible guard; no Lean, fixture child or cache advice',
        'gate_bytes': gate, 'first_compile_admission_and_preexec_share_this_gate': True,
        'cases': cases, 'passed': True,
        'hashes': {name: hashlib.sha256((B / name).read_bytes()).hexdigest() for name in ['check_gate_boundary.py', 'batch_context.py', 'child_runner.py', 'PLAN.json']}}
    with (B / 'gate-boundary.json').open('x') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
