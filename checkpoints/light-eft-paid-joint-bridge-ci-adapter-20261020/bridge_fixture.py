"""Finite owned-key prerequisite in the existing bounded bridge resolve child."""
from pathlib import Path
import hashlib,re
PREFIX='checkpoints/light-eft-bridge-audit-key-cache-20261021/staged/'
FIXTURE=PREFIX+'BridgeKeyEquivalenceFixtures.lean'
COMPOSITE=PREFIX+'ResolveAfterBridgeEquivalence.lean'
ORIGINAL='checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020/staged/ResolveBridgeTarget.lean'
FIXTURE_SHA='20759f3a9e7170d4fc08f4c26726b27335d33af3c781dc2b1875cf18f7130f79'
COMPOSITE_SHA='7a233bb04c37766093b5dfe21e1e1b79a1f628ee1b6eee0fba648e6717ee3410'
ORIGINAL_SHA='dd5741670280fc6b3a0f67791c23f6bf799730decf0e5c72342ed901c7fd6529'
MARKER='PASS: bridge owned-key serialization differential fixtures'
RESOLUTION_MARKER='PASS: official checker resolution is exactly [LightEFTPaidJointBridgeStage.SuppliedResponseJointBridge]'
HEADER=b'/- Reviewed bridge schedule: exact owned-key fixture, then unchanged singleton resolver. -/\n'
def require(ok,message):
    if not ok:raise ValueError(message)
def contract(spec):
    rows={r['role']:r for r in spec['sources']}
    require(len(rows)==len(spec['sources']),'Duplicate bridge source roles')
    for role,path,sha in [('resolver',COMPOSITE,COMPOSITE_SHA),('key_fixture',FIXTURE,FIXTURE_SHA),('original_resolver',ORIGINAL,ORIGINAL_SHA)]:
        require(rows.get(role,{}).get('path')==path and rows[role].get('sha256')==sha,'Bridge prerequisite authority differs: '+role)
def compose(fixture,resolver):
    require(fixture.startswith(b'import Lean\n') and resolver.startswith(b'import Lean\n'),'Expected exact single Lean import')
    return HEADER+fixture+b'\n'+resolver[len(b'import Lean\n'):]
def validate_sources(root,spec):
    contract(spec);root=Path(root)
    fixture=(root/FIXTURE).read_bytes();resolver=(root/ORIGINAL).read_bytes();composite=(root/COMPOSITE).read_bytes()
    require(hashlib.sha256(fixture).hexdigest()==FIXTURE_SHA and hashlib.sha256(resolver).hexdigest()==ORIGINAL_SHA and
            hashlib.sha256(composite).hexdigest()==COMPOSITE_SHA,'Bridge prerequisite source bytes differ')
    require(composite==compose(fixture,resolver),'Bridge prerequisite composition differs')
def validate_log(raw):
    require(not re.search(r'^(?:.*:\d+:\d+: )?(?:warning|error):',raw,re.M),'Bridge fixture/resolver warning or error')
    def positions(marker):
        return [m.start() for m in re.finditer(r'^(?:(?:[^\n]*:\d+:\d+: )?info: )?'+re.escape(marker)+r'$',raw,re.M)]
    first=positions(MARKER);second=positions(RESOLUTION_MARKER)
    require(len(first)==len(second)==1 and first[0]<second[0],'Missing/duplicate/reordered bridge key fixture prerequisite')
    return dict(fixture_sha256=FIXTURE_SHA,original_resolver_sha256=ORIGINAL_SHA,composite_sha256=COMPOSITE_SHA,
                fixture_marker=MARKER,resolver_marker=RESOLUTION_MARKER,fixture_before_resolver=True)
def receipt_prerequisite(stage,record,folder):
    require(stage=='resolve' and record.get('state')=='finished' and record.get('exit')==0 and 'failure' not in record,
            'Unsuccessful bridge prerequisite child')
    raw=(Path(folder)/'raw.log').read_bytes();binding=record.get('completed_logs',{}).get('raw.log',{})
    require(binding.get('bytes')==len(raw) and binding.get('sha256')==hashlib.sha256(raw).hexdigest(),'Bridge prerequisite completed log differs')
    result=validate_log(raw.decode())
    require(record.get('bridge_key_equivalence_fixture')==result,'Bridge prerequisite receipt differs')
    return result
