"""Exact canonical key fixture in the existing bounded singleton resolve child."""
from pathlib import Path
import hashlib, json, re

PREFIX = 'checkpoints/light-eft-canonical-key-cache-integration-20261022/staged/'
FIXTURE = PREFIX + 'CanonicalKeyEquivalenceFixtures.lean'
COMPOSITE = PREFIX + 'ResolveAfterCanonicalEquivalence.lean'
ORIGINAL = 'checkpoints/light-eft-canonical-output-adapter-20261020/staged/ResolveCanonicalOutputTarget.lean'
AUDIT = 'checkpoints/light-eft-canonical-output-adapter-20261020/staged/CanonicalOutputAudit.lean'
FIXTURE_SHA = '90c17220d76d30fa31ab2de59c129ec216c1202911db188c94f100373445a41e'
COMPOSITE_SHA = '20cf4392c2b711ba0cdb496f8a861d49a8eef28645334bb7e93bd53260e5a3c1'
ORIGINAL_SHA = '426579ed6d435c3644af7344c83eb320a7d4399769a8ae7a07a80ad78488f6dc'
AUDIT_SHA = '577b3f09c0702855d1f01e051574d8912c35565468b4e18611463b7b28d6ccec'
TARGET = 'LightEFTJointFlagOutputStage.PolynomialActualFailureProbability'
MARKER = 'PASS: canonical owned-key serialization differential fixtures'
RESOLUTION_MARKER = 'PASS: official checker resolution is exactly [' + TARGET + ']'
HEADER = b'/- Proposed canonical schedule: exact owned-key fixture, then unchanged singleton resolver. -/\n'
FLAGS = ('direct_reaped', 'all_descendants_gone', 'kernel_no_children_verified',
         'waitid_wait4_status_match', 'kernel_limits_verified', 'between_child_preservation_passed', 'preexec_binding_verified')

def require(ok, message):
    if not ok:
        raise ValueError(message)

def contract(spec):
    rows = spec['sources']
    require(set(rows) == {'source', 'audit', 'resolver', 'key_fixture', 'original_resolver'}, 'Canonical source roles differ')
    for role, path, sha in [('audit', AUDIT, AUDIT_SHA), ('resolver', COMPOSITE, COMPOSITE_SHA),
                            ('key_fixture', FIXTURE, FIXTURE_SHA), ('original_resolver', ORIGINAL, ORIGINAL_SHA)]:
        require(rows[role]['path'] == path and rows[role]['sha256'] == sha, 'Canonical prerequisite authority differs: ' + role)

def compose(fixture, resolver):
    require(fixture.startswith(b'import Lean\n') and resolver.startswith(b'import Lean\n'), 'Expected exact Lean import')
    return HEADER + fixture + b'\n' + resolver[len(b'import Lean\n'):]

def validate_sources(root, spec):
    contract(spec)
    root = Path(root)
    fixture, resolver, composite, audit = [(root / p).read_bytes() for p in [FIXTURE, ORIGINAL, COMPOSITE, AUDIT]]
    for raw, sha in [(fixture, FIXTURE_SHA), (resolver, ORIGINAL_SHA), (composite, COMPOSITE_SHA), (audit, AUDIT_SHA)]:
        require(hashlib.sha256(raw).hexdigest() == sha, 'Canonical prerequisite source bytes differ')
    require(composite == compose(fixture, resolver), 'Canonical prerequisite composition differs')
    start = b'private partial def appendNat'
    require(fixture.count(start) == audit.count(start) == 1, 'Canonical encoder helper is missing/duplicated')
    fixture_helper = fixture[fixture.index(start):fixture.index(b'\nend LightEFTAuditCollision')].rstrip()
    audit_helper = audit[audit.index(start):audit.index(b'\nprivate def hexKey')].rstrip()
    require(fixture_helper == audit_helper, 'Canonical fixture helper differs from submitted audit')

def validate_log(raw):
    require(raw and raw.endswith('\n'), 'Incomplete canonical fixture/resolver log')
    require(not re.search(r'^(?:.*:\d+:\d+: )?(?:warning|error):', raw, re.M), 'Canonical fixture/resolver warning or error')
    def positions(marker):
        return [m.start() for m in re.finditer(r'^(?:(?:[^\n]*:\d+:\d+: )?info: )?' + re.escape(marker) + r'$', raw, re.M)]
    first, second = positions(MARKER), positions(RESOLUTION_MARKER)
    require(raw.count(MARKER) == raw.count(RESOLUTION_MARKER) == 1 and len(first) == len(second) == 1 and first[0] < second[0],
            'Missing/duplicate/reordered canonical key fixture prerequisite')
    return dict(fixture_sha256=FIXTURE_SHA, original_resolver_sha256=ORIGINAL_SHA,
                composite_sha256=COMPOSITE_SHA, audit_sha256=AUDIT_SHA,
                fixture_marker=MARKER, resolver_marker=RESOLUTION_MARKER, fixture_before_resolver=True)

def completed_prerequisite(record, plan, folder, identity, lease):
    """Called before live replay/audit and after the full generic receipt verifier."""
    from contracts import bind
    require(plan['stage'] == record.get('stage') == 'resolve' and plan['module'] == TARGET, 'Wrong canonical prerequisite stage')
    require(record.get('state') == 'finished' and record.get('exit') == 0 and not record.get('failure') and
            not record.get('cleanup_errors') and record.get('synthetic_fixture') is False, 'Unsuccessful/synthetic canonical prerequisite')
    require(all(record.get(k) is True for k in FLAGS), 'Incomplete canonical prerequisite lifecycle/binding')
    require(identity and record.get('CI_identity') == identity and
            record.get('source_commit') == record.get('wrapper_commit') == identity['GITHUB_SHA'], 'Historical/different canonical prerequisite identity')
    require(record['argv'] == plan['argv'] and record['environment'] == plan['env'] and
            record['working_directory'] == plan['cwd'] and record['planned_source_bindings'] == plan['source_bindings'], 'Canonical prerequisite plan differs')
    require([r['path'] for r in record['submitted_sources']] == plan['sources'], 'Canonical prerequisite submissions differ')
    folder = Path(folder)
    for row, expected in zip(record['submitted_sources'], plan['source_bindings'], strict=True):
        require({k: row[k] for k in expected} == expected and row['snapshot'] == row['sha256'] + '.source', 'Canonical prerequisite source binding differs')
        bind(folder / row['snapshot'], row)
    require((record['lock']['device'], record['lock']['inode']) == (lease['device'], lease['inode']) and
            lease['acquired_ns'] <= record['started_ns'] < record['ended_ns'], 'Canonical prerequisite lease/timing differs')
    require(record.get('deadline_seconds') == 90.0 and record['handshake']['limits'] == {
        'RLIMIT_AS': [12 * 1024**3] * 2, 'RLIMIT_CPU': [60] * 2,
        'RLIMIT_FSIZE': [16 * 1024**2] * 2, 'RLIMIT_CORE': [0, 0]}, 'Canonical prerequisite child limits differ')
    who, terminal, pid = record['child_identity'], record['terminal_confirmation'], record['child_pid']
    require(who['pid'] == pid and who['ppid'] == record['supervisor_pid'] and who['sid'] == who['pgid'] == pid and
            terminal['terminal'] is True and terminal['pid'] == pid and terminal['status'] == 0, 'Canonical prerequisite owned terminal differs')
    require(record['runtime_wall_started_ns'] <= record['preexec_verified_ns'] <= terminal['finished_ns'] <
            record['runtime_wall_started_ns'] + 90 * 10**9, 'Canonical prerequisite deadline/terminal differs')
    observed = bind(folder / 'raw.log')
    require(record.get('completed_logs', {}).get('raw.log') == observed, 'Canonical prerequisite completed log binding differs')
    result = validate_log((folder / 'raw.log').read_text())
    require(record.get('canonical_key_equivalence_fixture') == result, 'Canonical prerequisite result differs')
    return dict(resolve_attempt_id=record['attempt_id'], resolve_ended_ns=record['ended_ns'],
                CI_identity=identity, completed_log=observed, fixture=result)

def verify_schedule(evidence, lease, plans, identity):
    """Full generic verification precedes this additional same-run prerequisite."""
    require(identity is not None and [p['stage'] for p in plans] == ['compile', 'resolve', 'replay', 'audit'] and
            all(p['module'] == TARGET for p in plans), 'Canonical fixture schedule/identity missing')
    evidence = Path(evidence)
    receipts = [json.loads((evidence / p['stage'] / 'receipt.json').read_text()) for p in plans]
    link = completed_prerequisite(receipts[1], plans[1], evidence / 'resolve', identity, lease)
    for plan, record in zip(plans, receipts, strict=True):
        require(record.get('CI_identity') == identity, 'Canonical receipt belongs to another run/attempt')
        if plan['stage'] in ['replay', 'audit']:
            require(record.get('canonical_key_equivalence_prerequisite') == link and
                    link['resolve_ended_ns'] < record['started_ns'], 'Missing/historical/unbound canonical prerequisite link')
    return link
