"""Offline exact insertion map; never compiles or executes Lean."""
from pathlib import Path
import json
H=Path(__file__).resolve().parent;R=H.parents[1]
AUDIT='checkpoints/light-eft-joint-flag-assignment-local-repair-20261018/staged/JointAssignmentLawAudit.lean'
PHASES=('frontend-ready','timing-helper-ready','scan-helper-ready','serialization-helper-ready',
        'audit-run-start','environment-ready','scan-complete','roots-complete','inventory-complete',
        'recursive-complete','interfaces-complete','inventory-written','dependencies-written',
        'imports-written','findings-written','strict-checks-complete')
CHANNEL_SCOPE='section LightEFTAuditDiagnosticChannel\nset_option stderrAsMessages false\n\n'
CHANNEL_END='\nend LightEFTAuditDiagnosticChannel\n'
FIRST=CHANNEL_SCOPE+'''/- Diagnostic only: fixed labels and a monotonic-millisecond clock modulo2^64.
No imported names, paths, expressions, payloads or environment variables are logged.
Each marker is flushed; all existing limits/checks and four exports are unchanged. -/
open Lean in
run_cmd do
  let now := (← IO.monoMsNow) % 18446744073709551616
  let out ← IO.getStderr
  out.putStrLn s!"AUDIT-TIMING: phase=frontend-ready mono-ms-mod64={now}"
  out.flush

namespace LightEFTAuditTiming
def mark (phase : String) : IO Unit := do
  let now := (← IO.monoMsNow) % 18446744073709551616
  let out ← IO.getStderr
  out.putStrLn s!"AUDIT-TIMING: phase={phase} mono-ms-mod64={now}"
  out.flush
end LightEFTAuditTiming

open Lean in
run_cmd do
  LightEFTAuditTiming.mark "timing-helper-ready"

'''
def top(phase):return '\nopen Lean in\nrun_cmd do\n  LightEFTAuditTiming.mark "'+phase+'"\n'
def mark(phase):return '  LightEFTAuditTiming.mark "'+phase+'"\n'
INSERTIONS=[
 ('import LightEFTJointFlagSamplingStage.JointAssignmentLaw\n\n',FIRST),
 ('end LightEFTAuditCollision\n',top('scan-helper-ready')),
 ('end LightEFTAuditText\n',top('serialization-helper-ready')),
 ('open Lean in\nrun_cmd do\n  let env :=',None),
 ('  let modules := env.allImportedModuleNames\n  let collisionReport',None),
 ('  let collisionReport ← LightEFTAuditCollision.scan env\n',mark('scan-complete')),
 ('  let mut textCache : LightEFTAuditText.Cache := {}\n',None),
 ('  let mut visited : NameSet := {}\n',None),
 ('  -- Require the exact reviewed deterministic and probability interfaces.\n',None),
 ('  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory\n',None),
 ('  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory\n',mark('inventory-written')),
 ('  IO.FS.writeFile "ci-evidence/recursive-dependencies.tsv" dependencies\n',mark('dependencies-written')),
 ('    (String.intercalate "\\n" (modules.toList.map toString) ++ "\\n")\n',mark('imports-written')),
 ('    (String.intercalate "\\n" issues.toList ++ "\\n")\n',mark('findings-written')),
 ('  if !issues.isEmpty then throwError "Strict focused audit rejected {issues.size} findings"\n',mark('strict-checks-complete'))]

def replacement(index,anchor,addition):
    if index==3:return anchor.replace('  let env :=',mark('audit-run-start')+'  let env :=')
    if index==4:return anchor.replace('  let collisionReport',mark('environment-ready')+'  let collisionReport')
    if index in [6,7,8,9]:
        phase={6:'roots-complete',7:'inventory-complete',8:'recursive-complete',9:'interfaces-complete'}[index]
        return mark(phase)+anchor
    return anchor+addition

def instrument(baseline):
    text=baseline
    for index,(anchor,addition) in enumerate(INSERTIONS):
        assert text.count(anchor)==1,('Insertion anchor not unique',index)
        text=text.replace(anchor,replacement(index,anchor,addition),1)
    return text+CHANNEL_END

def uninstrument(text):
    assert text.endswith(CHANNEL_END),'Diagnostic channel scope not restored'
    text=text[:-len(CHANNEL_END)]
    for index in reversed(range(len(INSERTIONS))):
        anchor,addition=INSERTIONS[index];added=replacement(index,anchor,addition)
        assert text.count(added)==1,('Instrumented insertion not unique',index)
        text=text.replace(added,anchor,1)
    return text

if __name__=='__main__':
    import subprocess
    base=subprocess.check_output(['git','-C',str(R),'show','7a7993f5c3a9c1efad1a7b8ca6c2a6c51031d03c:'+AUDIT]).decode()
    p=R/AUDIT
    assert p.read_text() in [base,instrument(base)],'Refuse to overwrite a different source delta'
    p.write_text(instrument(base))
    print(json.dumps(dict(status='OFFLINE_INSTRUMENTATION_ONLY',phases=len(PHASES),compiler_push_CI=False)))
