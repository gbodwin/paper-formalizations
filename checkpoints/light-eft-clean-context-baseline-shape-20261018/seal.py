"""Offline seal for exactly two preparation guards; no executor/compiler API."""
from pathlib import Path
import hashlib,json,subprocess

D=Path(__file__).resolve().parent;ROOT=D.parents[1]
A=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018'
C=ROOT/'checkpoints/light-eft-clean-context-corrections-20261018'
BASE='b74968f3f7c57c1a5768d902bfe1a2e910c8a055'
def sha(data):return hashlib.sha256(data).hexdigest()
def load(p):return json.loads(p.read_text())
def bind(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}

def main():
    p=load(D/'preservation.json');assert p['previous_bindings_verified']==91
    for r in p['preserved_files']:
        b=(D/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
    prior=D/'preserved-before-change'
    old=(prior/'clean_contract.py').read_text()
    baseline="        previous=launch\n        for s in samples:\n"
    replacement="        require(anon=={n['path']:n['memory_stat']['anon'] for n in baseline['nodes']},'Declared anonymous baseline differs from pre-exec snapshot')\n"+baseline
    assert old.count(baseline)==1
    expected=old.replace(baseline,replacement)
    first="        for s in samples:\n"
    assert expected.count(first)==1
    expected=expected.replace(first,first+"            require(isinstance(s,dict),'Runtime sample must be a dictionary')\n")
    assert (A/'clean_contract.py').read_text()==expected,'Broader core changes detected'
    assert (A/'REPORT.md').read_bytes().endswith((prior/'REPORT.md').read_bytes())
    historical=[]
    cm=load(C/'manifest.json')
    for r in cm['correction_files']:
        actual=bind(ROOT/r['repository_path']);assert actual==r;historical.append(actual)
    assert subprocess.check_output(['git','show',BASE+':'+str((C/'manifest.json').relative_to(ROOT))],cwd=ROOT)==(C/'manifest.json').read_bytes()
    historical.append(bind(C/'manifest.json'))
    for log in sorted(A.glob('tests-invocation-*.log')):
        assert subprocess.check_output(['git','show',BASE+':'+str(log.relative_to(ROOT))],cwd=ROOT)==log.read_bytes()
    # Proof/audit/chain artifacts and indexes are deliberately not regenerated.
    changed=subprocess.check_output(['git','diff','--name-only','-z',BASE],cwd=ROOT).decode().split('\0')
    changed=[s for s in changed if s]
    assert all(s.startswith(str(A.relative_to(ROOT))+'/') for s in changed)
    assert not any(s.endswith('.lean') for s in changed)
    assert not any(s.endswith(('chain-evidence-index.json','current-exact-source-evidence-20261018.json','audit_data.py')) for s in changed)
    validation=load(A/'packet-validation.json');assert validation['final_tests']==83 and not validation['production_enabled']
    validation.update(exact_core_guard_additions=2,previous_bindings_verified_before_edits=91,previous_correction_files_unchanged=len(historical),prior_test_histories_unchanged=True,accepted_proof_audit_and_indexes_unchanged=True)
    (D/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
    (A/'packet-validation.log').write_bytes((D/'validation.log').read_bytes())
    m=load(A/'manifest.json');m['correction_base_commit']=BASE;m['correction_report']=str((D/'REPORT.md').relative_to(ROOT))
    m['packet_files']=[]
    for f in sorted(A.rglob('*')):
        if f.is_file() and f!=A/'manifest.json':
            b=f.read_bytes();m['packet_files'].append({'path':str(f.relative_to(A)),'bytes':len(b),'sha256':sha(b)})
    for r in m['repository_evidence_updates']:r.update(bind(ROOT/r['repository_path']))
    (A/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
    current=[bind(A/r['path']) for r in m['packet_files']]+[bind(A/'manifest.json')]+m['repository_evidence_updates']
    files=[bind(f) for f in sorted(D.rglob('*')) if f.is_file() and f!=D/'manifest.json']
    result={'scope':'Exactly two disabled preparation guards and evidence refresh','base_commit':BASE,'frozen_mathematical_source':'78cb40c7837db049d645d73696f2e0b724ce8a3b','production_enabled':False,'correction_files':files,'current_preparation_bindings':current,'preserved_previous_correction_bindings':historical,'excluded':'Only this manifest excludes itself; immutable Git commit binds all files.'}
    (D/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'correction_files':len(files),'current_preparation_bindings':len(current),'preserved_previous_correction_bindings':len(historical),'tests':83,'targeted_regressions':3,'core_guard_additions':2},indent=2))

if __name__=='__main__':main()
