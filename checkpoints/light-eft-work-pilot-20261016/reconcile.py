"""Read-only source/object/log reconciliation; does not invoke Lean or a checker."""
from pathlib import Path
import json,hashlib,csv,re,subprocess
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence';OUT=ROOT/'.lake/work-pilot/lib/lean';PARENT=ROOT/'checkpoints/light-eft-edges-pilot-20261016'
h=lambda x:hashlib.sha256(x).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
rows=json.loads((E/'source-graph.json').read_text());state=json.loads((E/'fresh-build-state.json').read_text());oldstate=json.loads((PARENT/'evidence/fresh-build-state.json').read_text())
assert len(rows)==len(state)==486
rs=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len({r['attempt_id'] for r in rs})==len(rs)
assert len({(r['lock_device'],r['lock_inode']) for r in rs})==1
assert all(r['child_reaped'] for r in rs)
assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(rs,rs[1:]))
pre=[json.loads(x) for x in (E/'preflights.jsonl').read_text().splitlines()]
assert len(pre)==len(rs) and {x['attempt_id'] for x in pre}=={x['attempt_id'] for x in rs}
classification=[]
for r in rs:
 folder=E/'attempts'/r['attempt_id']
 assert h((folder/'preflight.json').read_bytes())==r['preflight_sha256']
 assert json.loads((folder/'preflight.json').read_text())['attempt_id']==r['attempt_id']
 for s in r['submitted_sources']:
  data=(folder/(s['sha256']+'.lean')).read_bytes();assert len(data)==s['bytes'] and h(data)==s['sha256']
 raw=(folder/'raw.log').read_text()
 classification.append(dict(attempt_id=r['attempt_id'],label=r['label'],exit=r['exit'],warning_headers=len(re.findall(r'^.*:\d+:\d+: warning(?:\([^)]*\))?:',raw,re.M)),error_headers=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',raw,re.M)),raw_sha256=h(raw.encode())))
 assert not classification[-1]['warning_headers']
 if r['exit']==0:assert not classification[-1]['error_headers']
save(E/'diagnostic-classification.json',dict(policy='Anchored source diagnostic headers only; hints and option names are not warnings.',attempts=classification))
objects=[];new=[];inherited=[]
for row in rows:
 n=row['module'];p=ROOT/row['path'];sha=h(p.read_bytes());obj=OUT/Path(*n.split('.')).with_suffix('.olean')
 assert sha==row['sha256']==state[n]['inputs']['source_sha256'] and h(obj.read_bytes())==state[n]['object_sha256']
 for d,sha_d in state[n]['inputs']['imports'].items():assert h((OUT/Path(*d.split('.')).with_suffix('.olean')).read_bytes())==sha_d
 good=[r for r in rs if r['label']=='fresh-compile-'+n and r['exit']==0 and r['submitted_sources'][0]['sha256']==sha]
 if good:new.append(n)
 else:
  assert state[n]==oldstate[n];inherited.append(n)
 objects.append(dict(module=n,path=row['path'],source_sha256=sha,object_path=str(obj),object_sha256=h(obj.read_bytes()),validation='new strict compilation' if good else 'byte-identical accepted inherited object',compile_receipt=good[-1]['attempt_id'] if good else None))
assert set(new)=={'LightEFTSpanners.ExecutableVotingWork','LightEFTSpanners'} and len(inherited)==484
assert [r['module'] for r in rows if r['sha256']!=r['reviewed_parent_sha256']]==['LightEFTSpanners.ExecutableVotingWork']
save(E/'source-object-provenance.json',objects)
for x in json.loads((E/'inherited-object-bindings.json').read_text())['objects']:
 assert h(Path(x['path']).read_bytes())==x['sha256']==oldstate[x['module']]['object_sha256']
audit=[r for r in rs if r['label']=='complete-all-owner-audit'][-1]
assert audit['exit']==1 and len(audit['submitted_sources'])==487
for s in audit['submitted_sources']:assert h(Path(s['path']).read_bytes())==s['sha256']
for f in ['CompleteAudit.lean','ResolveCheckerTarget.lean']:
 assert (PARENT/f).read_text().replace('light-eft-edges-pilot-20261016','light-eft-work-pilot-20261016')==(B/f).read_text()
inv=list(csv.DictReader((E/'diagnostic-actual-owner-inventory.tsv').open(),delimiter='\t'));deps=list(csv.DictReader((E/'diagnostic-recursive-dependencies.tsv').open(),delimiter='\t'));names={x['name'] for x in deps};assert len(names)==len(deps)
for x in deps:
 for k in ['typeDependencies','bodyDependencies']:assert set(filter(None,x[k].split(',')))<=names
assert {x['name'] for x in deps if x['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
before={x['name'] for x in json.loads((PARENT/'evidence/remaining-partial-roots.json').read_text())};partial={x['name'] for x in inv if x['partial']=='true'}
removed={'LightEFTSpanners.ExecutableVoting.'+n+'._unsafe_rec' for n in ['sampleWork','hostWork','edgesWork']}
assert before-partial==removed and not partial-before and len(partial)==52 and not removed&names
assert not any(x['unsafe']=='true' for x in inv) and not any(x['owner']=='LightEFTSpanners' for x in inv)
violations=(E/'diagnostic-strict-violations.txt').read_text().splitlines()
assert set(violations)=={'root partial: '+n for n in partial}|{'recursive partial: '+n for n in partial}
assert len(violations)==104
raw=(E/'attempts'/audit['attempt_id']/'raw.log').read_text();assert f'{len(inv)} actual-owner project declarations' in raw and f'{len(deps)} recursively visited constants' in raw and 'rejected 104' in raw
oldinv=list(csv.DictReader((PARENT/'evidence/diagnostic-actual-owner-inventory.tsv').open(),delimiter='\t'));oldnames={x['name']:x for x in oldinv};newnames={x['name']:x for x in inv};gone=sorted(oldnames.keys()-newnames.keys());added=sorted(newnames.keys()-oldnames.keys())
assert all(oldnames[n]['owner']=='LightEFTSpanners.ExecutableVotingWork' for n in gone)
assert all(newnames[n]['owner']=='LightEFTSpanners.ExecutableVotingWork' for n in added)
save(E/'owner-inventory-delta.json',dict(removed_partials=sorted(removed),added_partials=[],removed_roots=gone,added_roots=added))
save(E/'remaining-partial-roots.json',[x for x in inv if x['partial']=='true'])
replays=[r for r in rs if Path(r['argv'][0]).name=='leanchecker'];assert len(replays)==1;r=replays[0];target='LightEFTSpanners.ExecutableVotingWork'
assert r['exit']==0 and r['checker_resolution']['actual_modules']==[target]
assert (E/'attempts'/r['attempt_id']/'raw.log').read_text().strip()=='replaying '+target
resolution=json.loads((E/'pilot-target-resolution.json').read_text());assert resolution['count']==1 and resolution['resolved'][0]['module']==target
assert h(Path(resolution['resolved'][0]['object']).read_bytes())==state[target]['object_sha256']
assert any(r['label']=='pilot-semantics-and-safety' and r['exit']==0 for r in rs)
legacy=[r for r in rs if r['label']=='legacy-semantic-equivalence' and r['exit']==0][-1]
for x in legacy['submitted_sources']:assert h(Path(x['path']).read_bytes())==x['sha256']
preservation=[]
for name in ['light-eft-edges-pilot-20261016','light-eft-controller-pilot-20261016','light-eft-strict-aggregate-20261016']:
 p=ROOT/'checkpoints'/name;m=json.loads((p/'evidence-sha256.json').read_text())
 for x in m:
  data=(p/x['path']).read_bytes();assert len(data)==x['bytes'] and h(data)==x['sha256']
 preservation.append(dict(checkpoint=name,entries=len(m),all_hashes_match=True))
save(E/'prior-preservation.json',preservation)
summary=dict(new_strict_compiles=len(new),new_compile_modules=new,inherited_byte_identical_objects=len(inherited),complete_audit_fresh=True,clean_final_exact_source_gate_still_required=True,actual_owner_roots=len(inv),recursive_constants=len(deps),opaque_bodies=sum(x['kind']=='opaque' for x in deps),partial_roots=len(partial),removed_partials=sorted(removed),other_partial_roots_unchanged=True,unsafe_roots=0,aggregate_owned_roots=0,strict_gate_pass=False,new_source_bound_receipts=len(rs),persisted_preflights=len(pre),failed_attempts=[dict(uuid=r['attempt_id'],label=r['label'],exit=r['exit']) for r in rs if r['exit']],singleton_replays=1,actual_target_preflight=True,aggregate_prefix_not_invoked=True,nonoverlap=True,one_lock_inode=True,children_reaped=True,all_snapshot_hashes_verified=True,historical_qualifications=['Controller pilot: 494 persisted preflights for 495 receipts','Historical aggregate-prefix OOM/sequencing violation preserved','Prior edges pilot: incremental fresh-output validation using pinned dependency caches and byte-identical import hashes, not a clean final exact-source gate'])
save(E/'reconciliation.json',summary)
raw=(E/'diagnostic-recursive-dependencies.tsv').read_bytes();directory=B/'audit-export';directory.mkdir(exist_ok=True);parts=[];buf=b''
def emit(data):
 p=directory/('part-%03d.tsv'%len(parts));p.write_bytes(data);parts.append(dict(path=p.name,bytes=len(data),sha256=h(data)))
for line in raw.splitlines(keepends=True):
 if buf and len(buf)+len(line)>200000:emit(buf);buf=b''
 buf+=line
if buf:emit(buf)
save(directory/'manifest.json',dict(source='evidence/diagnostic-recursive-dependencies.tsv',bytes=len(raw),sha256=h(raw),parts=parts,reconstruction='Concatenate listed bytes in order without additional headers or separators.'))
print(json.dumps(dict(**summary,chunks=len(parts)),indent=2))
