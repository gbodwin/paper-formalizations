"""Offline finite implementation/source checks; never imports a runtime gate."""
from pathlib import Path
import ast,copy,hashlib,json,re,subprocess
H=Path(__file__).resolve().parent;R=H.parents[1]
BASE='4f06895ec9473b88b595904b77a453646f52f1e1'
B=R/'checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020'
P=R/'checkpoints/light-eft-paid-focused-adapter-20261020'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
sha=lambda b:hashlib.sha256(b).hexdigest()
c=ast.literal_eval((H/'finite_contract.py').read_text().split('CONTRACT=',1)[1])
old=ast.literal_eval((B/'finite_contract.py').read_text().split('CONTRACT=',1)[1])
s=json.loads((H/'ci-spec.json').read_text());plan=json.loads((H/'PLAN.json').read_text())
assert c['resources']==old['resources']==s['resource_contract']==plan['resource_contract']
assert c['pins']==old['pins']==s['pins'] and c['tool_hashes']==old['tool_hashes']==s['tool_hashes']
assert [len(c['imports'][m]) for m in c['modules']]==[81,82,83]
assert [len(c['required_roots'][m]) for m in c['modules']]==[10,20,6]
assert len(s['dependencies'])==81 and len(s['external_boundary_sources'])==30
assert s['execution_order']==[[m,k] for m in c['modules'] for k in ['compile','resolve','replay','audit']]
assert set(s['required_roots'])==set(s['required_interfaces'])==set(c['modules'])
for row in [*s['sources'],*s['dependencies'],*s['engine_files']]:
    raw=(R/row['path']).read_bytes();assert (len(raw),sha(raw))==(row['bytes'],row['sha256']),row['path']
for module,row in c['reviewed_sources'].items():
    raw=(R/row['path']).read_bytes();assert raw==git('show',BASE+':'+row['path'])
    assert (len(raw),sha(raw))==(row['bytes'],row['sha256'])
assert sha((R/'checkpoints/light-eft-flat-tape-law-20261021/staged/LightEFTFlatTapeStage/FlatTapeLaw.lean').read_bytes())=='b1d3beaa25f9528611b7ae85c86a41e4feda57b53c62b3a1ccb2cf6c28360ee9'
def funcs(path):
    return {n.name:ast.dump(n,include_attributes=False) for n in ast.walk(ast.parse(path.read_text())) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
assert funcs(H/'batch_context.py')==funcs(B/'bridge_context.py')
assert (H/'audit_check.py').read_bytes()==(B/'audit_check.py').read_bytes()
a,b=funcs(H/'output_guards.py'),funcs(B/'output_guards.py')
assert set(a)==set(b) and all(a[k]==b[k] for k in a if k!='focused_contract')
a,b=funcs(H/'prior_guard.py'),funcs(B/'prior_guard.py')
assert all(a[k]==b[k] for k in b if k not in ['verify','expected_roots'])
assert (H/'same_run.py').read_text().startswith((B/'same_run.py').read_text())
template=(B/'staged/BridgeAudit.lean').read_text();oldline=next(x for x in template.splitlines() if 'let requiredRoots : Array Name :=' in x)
oldmodule=old['modules'][0]
for module,name in zip(c['modules'],['FlatTapeAudit','FairBitAudit','IndependentTapeAudit'],strict=True):
    raw=(H/'staged'/(name+'.lean')).read_text()
    line=next(x for x in raw.splitlines() if 'let requiredRoots : Array Name :=' in x)
    assert raw.replace(module,oldmodule).replace(line,oldline)==template
    assert all(json.dumps(n)+'.toName' in line for n in c['required_roots'][module])
resolver=(B/'staged/ResolveBridgeTarget.lean').read_text().replace('[`'+oldmodule+']','['+', '.join('`'+m for m in c['modules'])+']')
assert (H/'staged/ResolveBatchTarget.lean').read_text()==resolver

specpaths=['checkpoints/'+n+'/ci-spec.json' for n in [
 'light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
 'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020']]
binding_changes=[]
for path in specpaths:
    before=json.loads(git('show',BASE+':'+path));after=json.loads((R/path).read_text());expected=copy.deepcopy(before)
    for i,row in enumerate(expected['engine_files']):
        if row['path'] in ['.github/workflows/lean.yml',*specpaths]:
            raw=(R/row['path']).read_bytes();new=dict(path=row['path'],bytes=len(raw),sha256=sha(raw))
            if new!=row:binding_changes.append(dict(spec=path,path=row['path']))
            expected['engine_files'][i]=new
    assert after==expected,path

workflow=git('show',BASE+':.github/workflows/lean.yml').decode()
dep='      - name: Build exact external inputs for fair-bit batch\n        run: lake build +Mathlib.Analysis.SpecificLimits.Normed +Mathlib.Topology.Algebra.InfiniteSum.ENNReal +Mathlib.Tactic.FieldSimp\n'
workflow=workflow.replace('      - name: Check all paper module indexes\n',dep+'      - name: Check all paper module indexes\n')
newblock='''      - name: Verify reviewed flat tape and fair-bit sampler batch
        id: light_eft_fair_bit_batch
        env:
          PYTHONPYCACHEPREFIX: ${{ runner.temp }}/light-eft-fair-bit-batch-python-${{ github.run_id }}-${{ github.run_attempt }}
        run: python3 -B checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci_gate.py
      - name: Preserve fair-bit batch evidence before remaining checks
        if: ${{ always() && steps.light_eft_fair_bit_batch.outcome != 'skipped' }}
        uses: actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02
        with:
          name: light-eft-fair-bit-batch-${{ github.run_id }}-${{ github.run_attempt }}
          path: ${{ runner.temp }}/light-eft-fair-bit-batch-${{ github.run_id }}-${{ github.run_attempt }}
          include-hidden-files: true
          if-no-files-found: error
          retention-days: 30
'''
workflow=workflow.replace('      - name: Verify canonical actual-output corollary after three context replays\n',newblock+'      - name: Verify canonical actual-output corollary after three context replays\n')
workflow=workflow.replace('          LIGHTEFT_SUMMARY_COROLLARY_OUTCOME:','          LIGHTEFT_SUMMARY_BATCH_OUTCOME: ${{ steps.light_eft_fair_bit_batch.outcome }}\n          LIGHTEFT_SUMMARY_COROLLARY_OUTCOME:')
workflow=workflow.replace("              ('corollary_step_outcome', 'LIGHTEFT_SUMMARY_COROLLARY_OUTCOME')]}","              ('corollary_step_outcome', 'LIGHTEFT_SUMMARY_COROLLARY_OUTCOME'),\n              ('fair_bit_batch_step_outcome', 'LIGHTEFT_SUMMARY_BATCH_OUTCOME')]}")
needle='            ${{ runner.temp }}/light-eft-paid-joint-bridge-${{ github.run_id }}-${{ github.run_attempt }}\n'
workflow=workflow.replace(needle,needle+'            ${{ runner.temp }}/light-eft-fair-bit-batch-${{ github.run_id }}-${{ github.run_attempt }}\n')
assert (R/'.github/workflows/lean.yml').read_text()==workflow
assert 'timeout-minutes: 120' in workflow
budget=plan['budget_qualification'];assert budget['job_timeout_minutes']==120 and budget['observed_remaining_minutes']==11.1
assert 'unmeasured' in budget['new_batch_duration'] and 'failure' in budget['timeout_policy']
allowed={'.github/workflows/lean.yml',*specpaths}
prefix=str(H.relative_to(R))+'/'
changed=git('diff','--name-only',BASE).decode().splitlines()
assert all(p in allowed or p.startswith(prefix) for p in changed)
assert all(p.startswith(prefix) for p in git('ls-files','--others','--exclude-standard').decode().splitlines())
for p in H.glob('*.py'):ast.parse(p.read_text())
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_OFFLINE_IMPLEMENTATION_BINDINGS_ONLY',
    reviewed_mathematics_preserved=True,inherited_context_methods_unchanged=True,
    live_guard_functions_unchanged_except_finite_ledger=True,collision_and_recursive_audit_body_unchanged=True,
    accepted_producer_authentication_prefix_preserved=True,old_specs_binding_only=binding_changes,
    sources=len(s['sources']),base_project_dependencies=81,external_boundary_sources=30,
    project_closures=['81/82','82/83','83/84'],new_native_schedule=12,
    resource_controls_unchanged=True,job_budget_fit='NOT ESTABLISHED; REVIEW REQUIRED',
    no_compiler_push_CI=True,independent_implementation_review='pending',kernel_acceptance=False),indent=2))
