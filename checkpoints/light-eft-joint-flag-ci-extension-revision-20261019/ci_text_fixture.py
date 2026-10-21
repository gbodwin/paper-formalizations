"""Finite serialization prerequisite within the existing bounded resolve child."""
from pathlib import Path
import hashlib,re

PREFIX='checkpoints/light-eft-audit-text-fixture-adapter-20261021/'
FIXTURE='checkpoints/light-eft-audit-text-cache-20261021/staged/SerializationEquivalenceFixtures.lean'
ORIGINAL='checkpoints/light-eft-joint-flag-assignment-corrected-draft-20261018/staged/ResolveJointAssignmentLawTarget.lean'
COMPOSITE=PREFIX+'staged/ResolveAfterTextEquivalence.lean'
FIXTURE_SHA='4145f3211fec079581cc3b4f6645c77f1620abb02f503b12a4e1cdd333d944c0'
ORIGINAL_SHA='4f887745e6bc31d390fa04e2e3e91fa6fe6d3911623796974b24ca7a8fc6964a'
MARKER='PASS: pure name-text serialization differential fixtures'
RESOLUTION_MARKER='PASS: official checker resolution is exactly [LightEFTJointFlagSamplingStage.JointAssignmentLaw]'
HEADER=b'/- Reviewed schedule: exact serialization fixture, then unchanged singleton resolver. -/\n'

def require(condition,message):
    if not condition:raise ValueError(message)

def contract(spec):
    for key,path in [('resolver',COMPOSITE),('serialization_fixture',FIXTURE),('original_resolver',ORIGINAL)]:
        require(spec['sources'].get(key,{}).get('path')==path,'Serialization prerequisite authority path differs: '+key)
    require(spec['sources']['serialization_fixture']['sha256']==FIXTURE_SHA and
            spec['sources']['original_resolver']['sha256']==ORIGINAL_SHA,'Reviewed fixture/resolver authority differs')

def compose(fixture,resolver):
    require(fixture.startswith(b'import Lean\n') and resolver.startswith(b'import Lean\n'),'Exact single Lean import required')
    return HEADER+fixture+b'\n'+resolver[len(b'import Lean\n'):]

def validate_sources(root,spec):
    contract(spec);root=Path(root)
    fixture=(root/FIXTURE).read_bytes();resolver=(root/ORIGINAL).read_bytes()
    require(hashlib.sha256(fixture).hexdigest()==FIXTURE_SHA and hashlib.sha256(resolver).hexdigest()==ORIGINAL_SHA,
            'Reviewed prerequisite source bytes differ')
    require((root/COMPOSITE).read_bytes()==compose(fixture,resolver),'Composite prerequisite schedule differs')

def validate_log(raw):
    # Lean run_cmd logInfo may be plain or carry the standard info/location prefix.
    # Reject substring/duplicate/reordered markers and all Lean diagnostics.
    require(not re.search(r'^(?:.*:\d+:\d+: )?(?:warning|error):',raw,re.M),'Fixture/resolver warning or error')
    def positions(marker):
        return [m.start() for m in re.finditer(r'^(?:(?:[^\n]*:\d+:\d+: )?info: )?'+re.escape(marker)+r'$',raw,re.M)]
    first=positions(MARKER);second=positions(RESOLUTION_MARKER)
    require(len(first)==len(second)==1 and first[0]<second[0],'Missing/duplicate/reordered serialization prerequisite success')
    return dict(fixture_sha256=FIXTURE_SHA,original_resolver_sha256=ORIGINAL_SHA,
                fixture_marker=MARKER,resolver_marker=RESOLUTION_MARKER,fixture_before_resolver=True)

def receipt_prerequisite(stage,record,folder):
    require(record.get('state')=='finished' and record.get('exit')==0 and 'failure' not in record,
            'Unsuccessful prerequisite child')
    require(stage=='resolve' and 'raw.log' in record.get('completed_logs',{}),'Missing bound prerequisite log')
    raw=(Path(folder)/'raw.log').read_bytes();binding=record['completed_logs']['raw.log']
    require(binding.get('bytes')==len(raw) and binding.get('sha256')==hashlib.sha256(raw).hexdigest(),
            'Prerequisite completed-log hash differs')
    result=validate_log(raw.decode())
    require(record.get('serialization_equivalence_fixture')==result,'Prerequisite receipt evidence differs')
    return result
