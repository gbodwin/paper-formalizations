"""Pure checks for split visible/host gates; no child or cache advice."""
import copy
import datetime
import json
from pathlib import Path
import pilot_runner as p
import decision_telemetry as telemetry

assert p.ADMISSION_VISIBLE_HEADROOM == 4294967296
assert p.ADMISSION_HEADROOM == 3221225472 and p.STOP_HEADROOM == 1073741824
base = {'headroom': 8 * 1024**3, 'system_available': 8 * 1024**3,
        'nodes': [{'path': '/synthetic', 'limit': str(16 * 1024**3), 'oom': {'oom': 0},
                   'pids_max': 'max', 'pids_events': {'max': 0}, 'pids_current': 1}]}
checks = {}
for field, threshold in [('headroom', p.ADMISSION_VISIBLE_HEADROOM), ('system_available', p.ADMISSION_HEADROOM)]:
    for delta in [0, -1]:
        now = copy.deepcopy(base)
        now[field] = threshold + delta
        sample = {'collection_errors': [], 'accounting': now, 'child': {'state': 'S', 'rss': 1}}
        errors = telemetry.policy_errors(sample, base, None, p.ADMISSION_VISIBLE_HEADROOM,
                                         p.RSS_STOP, p.ANON_GROWTH_STOP, p.check_memory, p.ADMISSION_HEADROOM)
        key = field + ('_at_gate_passes' if delta == 0 else '_below_gate_stops')
        checks[key] = (not errors) if delta == 0 else bool(errors)
        assert checks[key], (key, errors)
now = copy.deepcopy(base)
now.update(headroom=p.ADMISSION_VISIBLE_HEADROOM, system_available=p.ADMISSION_HEADROOM)
checks['visible_4GiB_host_3GiB_passes'] = not telemetry.policy_errors(
    {'collection_errors': [], 'accounting': now, 'child': {'state': 'S', 'rss': 1}}, base, None,
    p.ADMISSION_VISIBLE_HEADROOM, p.RSS_STOP, p.ANON_GROWTH_STOP, p.check_memory, p.ADMISSION_HEADROOM)
assert all(checks.values())
for stage in ['compile', 'resolve']:
    try:
        p.stage_argv(stage)
    except ValueError:
        checks[stage + '_disabled'] = True
    else:
        raise AssertionError('Unauthorized stage enabled')
result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'checks': checks,
          'scope': 'Pure synthetic boundary checks only; no live child, cache pass, or advice'}
with (Path(__file__).resolve().parent / 'boundary-checks.json').open('x') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
print(json.dumps(result, indent=2))
