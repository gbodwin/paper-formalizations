"""Pure assertions for the one changed admission constant; no live child fixtures."""
import copy
import datetime
import json
from pathlib import Path
import pilot_runner as p
import decision_telemetry as telemetry

assert p.ADMISSION_HEADROOM == 3221225472
assert p.STOP_HEADROOM == 1073741824
assert p.RSS_STOP == 6442450944 and p.ANON_GROWTH_STOP == 3221225472
assert p.LIMITS == {'RLIMIT_AS': 12884901888, 'RLIMIT_CPU': 60,
                    'RLIMIT_FSIZE': 16777216, 'RLIMIT_CORE': 0}
assert p.INTERVAL == .1 and p.DEADLINE == 90
baseline = {'headroom': 8 * 1024**3, 'system_available': 8 * 1024**3,
            'nodes': [{'path': '/synthetic/group', 'limit': str(16 * 1024**3),
                       'oom': {'oom': 0}, 'pids_max': 'max',
                       'pids_events': {'max': 0}, 'pids_current': 1}]}
checks = {}
for field in ['headroom', 'system_available']:
    for delta, should_pass in [(0, True), (-1, False)]:
        now = copy.deepcopy(baseline)
        now[field] = p.ADMISSION_HEADROOM + delta
        decision = {'collection_errors': [], 'accounting': now,
                    'child': {'state': 'S', 'rss': 1}}
        errors = telemetry.policy_errors(decision, baseline, None, p.ADMISSION_HEADROOM,
                                         p.RSS_STOP, p.ANON_GROWTH_STOP, p.check_memory)
        name = field + ('_at_3GiB_passes' if delta == 0 else '_one_byte_below_stops')
        checks[name] = (not errors) == should_pass
        assert checks[name], (name, errors)
assert all(checks.values())
result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'scope': 'Four pure synthetic admission/pre-exec boundary assertions; no live diagnostic or fixture child',
          'admission_visible_and_host_bytes': p.ADMISSION_HEADROOM,
          'unchanged_ongoing_floor_bytes': p.STOP_HEADROOM, 'checks': checks,
          'compiler_or_checker_started': False}
path = Path(__file__).resolve().parent / 'admission-boundary-checks.json'
with path.open('x') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
print(json.dumps(result, indent=2))
