"""Seal offline correction evidence. No compiler, retrieval or executor API."""
from pathlib import Path
import copy,hashlib,json,subprocess

C=Path(__file__).resolve().parent;ROOT=C.parents[1]
A=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018'
BASE='83cd543c23fbf7349e82baa61cfccf1b2e27da4d'
def sha(data):return hashlib.sha256(data).hexdigest()
def load(p):return json.loads(p.read_text())
def binding(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}

def main():
    preservation=load(C/'preservation.json');assert preservation['verified_prior_manifest_entries']==59
    for r in preservation['preserved_files']:
        p=C/r['preserved_path'];assert binding(p)['sha256']==r['sha256']
    logs=[]
    for n in range(1,5):
        p=A/('tests-invocation-%02d.log'%n)
        old=subprocess.check_output(['git','show',BASE+':'+str(p.relative_to(ROOT))],cwd=ROOT)
        assert old==p.read_bytes();logs.append(binding(p))
    prior=C/'preserved-before-correction'/A.relative_to(ROOT)
    assert (A/'REPORT.md').read_bytes().endswith((prior/'REPORT.md').read_bytes())
    before=load(prior/'chain-evidence-index.json');after=load(A/'chain-evidence-index.json')
    normalized_before=copy.deepcopy(before);normalized_after=copy.deepcopy(after)
    for d in [normalized_before,normalized_after]:
        d['full_audit'].pop('review_status');d['full_audit'].pop('verification_attribution',None)
    assert normalized_before==normalized_after,'Accepted chain/audit results changed'
    index='Light Edge Fault Tolerant Graph Spanners/verification/current-exact-source-evidence-20261018.json'
    current=load(ROOT/index);original=load(C/'preserved-before-correction'/index)
    for d in [current,original]:
        d.pop('chain_index');d['full_audit'].pop('review_status');d['full_audit'].pop('verification_attribution',None)
    assert current==original,'Dated mathematical/evidence scope changed'
    validation=load(A/'packet-validation.json')
    assert validation['final_tests']==80 and not validation['production_enabled']
    validation.update(previous_packet_manifest_bindings_verified_before_edits=59,preserved_test_histories=logs,accepted_chain_and_audit_results_unchanged=True,original_preparation_report_preserved_as_suffix=True)
    (C/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
    # The original validator raw log is preserved in the before-correction tree.
    (A/'packet-validation.log').write_bytes((C/'validation.log').read_bytes())
    m=load(A/'manifest.json');m['correction_base_commit']=BASE
    m['correction_report']=str((C/'REPORT.md').relative_to(ROOT))
    m['packet_files']=[]
    for p in sorted(A.rglob('*')):
        if not p.is_file() or p==A/'manifest.json':continue
        b=p.read_bytes();m['packet_files'].append({'path':str(p.relative_to(A)),'bytes':len(b),'sha256':sha(b)})
    for r in m['repository_evidence_updates']:
        r.update(binding(ROOT/r['repository_path']))
    (A/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
    entries=[binding(p) for p in sorted(C.rglob('*')) if p.is_file() and p!=C/'manifest.json']
    updates=[binding(A/r['path']) for r in m['packet_files'] if (A/r['path']).is_file()]
    updates+=[binding(A/'manifest.json')]+m['repository_evidence_updates']
    result={'scope':'Preparation-only Light EFT correction; production disabled','base_commit':BASE,'frozen_mathematical_source':'78cb40c7837db049d645d73696f2e0b724ce8a3b','production_enabled':False,'correction_files':entries,'current_preparation_and_evidence_bindings':updates,'excluded':'Only this manifest excludes itself; immutable Git commit binds all files.'}
    (C/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'correction_files':len(entries),'current_preparation_and_evidence_bindings':len(updates),'original_test_logs_preserved':4,'tests':80,'accepted_proof_audit_results_unchanged':True},indent=2))

if __name__=='__main__':main()
