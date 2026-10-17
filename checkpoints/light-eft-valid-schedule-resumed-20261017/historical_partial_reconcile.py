"""Reconcile a memory-blocked partial checkpoint without invoking Lean/checker."""
from pathlib import Path
import json,hashlib,subprocess,re
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence';PARENT=ROOT/'checkpoints/light-eft-candidates-selected-pilot-20261017';OUT=ROOT/'.lake/valid-schedule-pilot/lib/lean'
h=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((E/'source-graph.json').read_text());state=json.loads((E/'fresh-build-state.json').read_text());oldstate=json.loads((PARENT/'evidence/fresh-build-state.json').read_text());aff=json.loads((E/'affected-closure.json').read_text())
assert len(rows)==486 and len(aff['modules'])==147 and len(state)==340
changed=[r['module'] for r in rows if r['sha256']!=r['reviewed_parent_sha256']];assert changed==['LightEFTSpanners.StoredCandidateRefinement']
for r in rows:assert h((ROOT/r['path']).read_bytes())==r['sha256']
old=(E/'StoredCandidateRefinement.before.lean.txt').read_text();new=(ROOT/'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/StoredCandidateRefinement.lean').read_text()
assert old.split('def ValidSchedule ')[0]==new.split('def ValidSchedule ')[0]
assert old[old.index('def originalStep '):]==new[new.index('def originalStep '):]
from declarations import declarations
headers={n:d['header'] for n,d in declarations(old).items() if d['kind']=='theorem'};current=declarations(new);assert len(headers)==3 and all(current[n]['header']==v for n,v in headers.items())
receipts=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len(receipts)==2 and {r['label'] for r in receipts}=={'legacy-semantic-equivalence','fresh-compile-LightEFTSpanners.StoredCandidateRefinement'}
assert len({r['attempt_id'] for r in receipts})==2 and len({(r['lock_device'],r['lock_inode']) for r in receipts})==1
assert all(r['exit']==0 and r['child_reaped'] for r in receipts)
assert receipts[0]['end_monotonic_ns']<receipts[1]['start_monotonic_ns']
pre=[json.loads(x) for x in (E/'preflights.jsonl').read_text().splitlines()];assert len(pre)==2
ad=[json.loads(x) for x in (E/'memory-admissions.jsonl').read_text().splitlines()];assert len(ad)==3 and [a['admitted'] for a in ad]==[True,True,False]
assert ad[-1]['label']=='pilot-semantics-and-safety' and ad[-1]['cgroup_headroom']<ad[-1]['required_available_bytes']==4294967296
for a,r in zip(ad,receipts):assert a['label']==r['label'] and a['monotonic_ns']<=r['start_monotonic_ns']
snapshots=0
for r in receipts:
 folder=E/'attempts'/r['attempt_id'];assert h((folder/'preflight.json').read_bytes())==r['preflight_sha256']
 for x in r['submitted_sources']:
  data=(folder/(x['sha256']+'.lean')).read_bytes();assert h(data)==x['sha256'] and len(data)==x['bytes'];snapshots+=1
 raw=(folder/'raw.log').read_text();assert not re.search(r'^.*:\d+:\d+: (warning|error)',raw,re.M)
 if r['label']=='legacy-semantic-equivalence':
  ax=re.findall(r'depends on axioms: \[(.*?)\]',raw,re.S);assert ax and set(ax[0].replace('\n','').replace(' ','').split(','))=={'propext','Classical.choice','Quot.sound'} and 'sorryAx' not in raw
objects=[]
for n,x in state.items():
 p=OUT/Path(*n.split('.')).with_suffix('.olean');assert h(p.read_bytes())==x['object_sha256']
 row=next(r for r in rows if r['module']==n);assert x['inputs']['source_sha256']==row['sha256']
 for d,sha in x['inputs']['imports'].items():assert h((OUT/Path(*d.split('.')).with_suffix('.olean')).read_bytes())==sha
 if n!='LightEFTSpanners.StoredCandidateRefinement':assert x==oldstate[n] and n not in aff['modules']
 objects.append({'module':n,'source_sha256':row['sha256'],'object_sha256':x['object_sha256'],'status':'fresh strict compile' if n=='LightEFTSpanners.StoredCandidateRefinement' else 'accepted inherited binding'})
for x in json.loads((E/'inherited-object-bindings.json').read_text())['objects']:assert h(Path(x['path']).read_bytes())==x['sha256']
for filename in ['SequentialLean.py','MemoryAdmission.py']:
 assert (B/filename).read_bytes()==(PARENT/filename).read_bytes()
for filename in ['CompleteAudit.lean','ResolveCheckerTarget.lean']:
 assert (B/filename).read_text()==(PARENT/filename).read_text().replace('light-eft-candidates-selected-pilot-20261017','light-eft-valid-schedule-pilot-20261017')
for x in json.loads((E/'toolchain-and-supervisor-hashes.json').read_text()):
 p=Path(x['path']);p=p if p.is_absolute() else ROOT/p;assert h(p.read_bytes())==x['sha256']
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
for x in pins:assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=Path('/workspace/paper-formalizations/.lake/packages')/x['name'],text=True).strip()==x['rev']
prior=json.loads((PARENT/'evidence/prior-preservation.json').read_text());names=[PARENT.name]+[x['checkpoint'] for x in prior];pres=[]
for name in names:
 p=ROOT/'checkpoints'/name;m=json.loads((p/'evidence-sha256.json').read_text())
 for x in m:
  data=(p/x['path']).read_bytes();assert h(data)==x['sha256'] and len(data)==x['bytes']
 pres.append({'checkpoint':name,'entries':len(m),'all_hashes_match':True})
summary={'status':'blocked partial; not accepted','fresh_strict_compiles':1,'affected_required':147,'affected_pending':146,'inherited_bound_objects':339,'completed_receipts':2,'submitted_source_entries':snapshots,'memory_admissions':3,'refused_admissions':1,'fixture_compiler_started':False,'fresh_audit_run':False,'singleton_replay_run':False,'fresh_partial_root_count':None,'accepted_baseline_partial_roots':12,'accepted_baseline_findings':24,'nonoverlap':True,'one_lock_inode':True,'all_children_reaped':True,'all_snapshot_hashes_verified':True,'three_old_statements_unchanged':True,'all_other_roots_unchanged':True,'failure':'Memory admission refusal, not a Lean diagnostic','refused_headroom_bytes':ad[-1]['cgroup_headroom'],'required_headroom_bytes':4294967296}
for name,data in [('partial-reconciliation.json',summary),('source-object-provenance.json',objects),('prior-preservation.json',pres)]: (E/name).write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(summary,indent=2))
