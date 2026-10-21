"""Offline exact port from reviewed70492ce7; no runtime or remote authority."""
from pathlib import Path
import hashlib,subprocess
H=Path(__file__).resolve().parent;R=H.parents[1]
BASE='70492ce724a942392d94d13ca273c4a0aa208628'
BRIDGE='checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020/'
AUDIT=BRIDGE+'staged/BridgeAudit.lean'
ORIGINAL=BRIDGE+'staged/ResolveBridgeTarget.lean'
DECODER='checkpoints/light-eft-joint-flag-assignment-local-repair-20261018/staged/JointAssignmentLawAudit.lean'
FIXTURE=str(H.relative_to(R))+'/staged/BridgeKeyEquivalenceFixtures.lean'
COMPOSITE=str(H.relative_to(R))+'/staged/ResolveAfterBridgeEquivalence.lean'
MARKER='PASS: bridge owned-key serialization differential fixtures'
PHASES=('frontend-ready','timing-helper-ready','scan-helper-ready','audit-run-start','environment-ready','scan-complete',
        'roots-complete','inventory-complete','recursive-complete','interfaces-complete',
        'inventory-written','dependencies-written','imports-written','findings-written','strict-checks-complete')
def base(path,rev=BASE):return subprocess.check_output(['git','-C',str(R),'show',rev+':'+path]).decode()
def block(s):return s[s.index('namespace LightEFTAuditCollision'):s.index('end LightEFTAuditCollision')+len('end LightEFTAuditCollision')]
def mark(label):return '  LightEFTBridgeAuditTiming.mark "'+label+'"\n'
def audit_source():
    old=base(AUDIT);decoder=base(DECODER)
    assert block(old)==block(base(DECODER,'c46b0a6b66a67b86d5de7a16f3bf38983571d2a5'))
    s=old.replace(block(old),block(decoder),1)
    top=decoder[decoder.index('section LightEFTAuditDiagnosticChannel'):decoder.index('/- Verification helper only.')]
    top=top.replace('LightEFTAuditDiagnosticChannel','LightEFTBridgeAuditDiagnosticChannel').replace('LightEFTAuditTiming','LightEFTBridgeAuditTiming').replace('AUDIT-TIMING: ','BRIDGE-AUDIT-TIMING: ')
    prefix='import Lean\nimport LightEFTPaidJointBridgeStage.SuppliedResponseJointBridge\n\n'
    assert s.startswith(prefix);s=s.replace(prefix,prefix+top,1)
    end='end LightEFTAuditCollision\n';assert s.count(end)==1
    s=s.replace(end,end+'\nopen Lean in\nrun_cmd do\n'+mark('scan-helper-ready'),1)
    cut=s.index('/- Unexecuted focused audit draft.');pre,body=s[:cut],s[cut:]
    edits=[('run_cmd do\n','run_cmd do\n'+mark('audit-run-start')),
      ('  let modules := env.allImportedModuleNames\n','  let modules := env.allImportedModuleNames\n'+mark('environment-ready')),
      ('  let collisionReport ← LightEFTAuditCollision.scan env\n','  let collisionReport ← LightEFTAuditCollision.scan env\n'+mark('scan-complete')),
      ('  let mut inventory :=',mark('roots-complete')+'  let mut inventory :='),
      ('  let mut visited : NameSet :=',mark('inventory-complete')+'  let mut visited : NameSet :='),
      ('  -- Require the exact reviewed deterministic and probability interfaces.\n',mark('recursive-complete')+'  -- Require the exact reviewed deterministic and probability interfaces.\n'),
      ('  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory\n',mark('interfaces-complete')+'  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory\n'+mark('inventory-written')),
      ('  IO.FS.writeFile "ci-evidence/recursive-dependencies.tsv" dependencies\n','  IO.FS.writeFile "ci-evidence/recursive-dependencies.tsv" dependencies\n'+mark('dependencies-written')),
      ('    (String.intercalate "\\n" (modules.toList.map toString) ++ "\\n")\n','    (String.intercalate "\\n" (modules.toList.map toString) ++ "\\n")\n'+mark('imports-written')),
      ('    (String.intercalate "\\n" issues.toList ++ "\\n")\n','    (String.intercalate "\\n" issues.toList ++ "\\n")\n'+mark('findings-written')),
      ('  if !issues.isEmpty then throwError "Strict focused audit rejected {issues.size} findings"\n','  if !issues.isEmpty then throwError "Strict focused audit rejected {issues.size} findings"\n'+mark('strict-checks-complete'))]
    for a,b in edits:assert body.count(a)==1,a;body=body.replace(a,b,1)
    return pre+body+'\nend LightEFTBridgeAuditDiagnosticChannel\n'
def fixture_source():
    decoder=base('checkpoints/light-eft-audit-text-cache-20261021/staged/SerializationEquivalenceFixtures.lean')
    prefix=decoder.split('/- Source-only fixture for future reviewed bounded validation.',1)[0]
    assert prefix.startswith('import Lean\n') and 'run_cmd do' in prefix
    return prefix.rstrip()+'\n  logInfo "'+MARKER+'"\n'
HEADER=b'/- Reviewed bridge schedule: exact owned-key fixture, then unchanged singleton resolver. -/\n'
def composite_source():return (HEADER+fixture_source().encode()+b'\n'+base(ORIGINAL).encode()[len(b'import Lean\n'):]).decode()
if __name__=='__main__':
    for path,s in [(AUDIT,audit_source()),(FIXTURE,fixture_source()),(COMPOSITE,composite_source())]:(R/path).write_text(s)
