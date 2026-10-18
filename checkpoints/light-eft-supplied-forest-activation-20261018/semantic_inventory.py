"""Strict semantic inventory plus separately observed local IR signatures.
Excluded files are stat'ed, never content-hashed. No execution/locking API."""
from pathlib import Path
import collections,copy,hashlib,json,os,stat,subprocess
from contracts import *
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
DATA=('inventory-policy.json','signature-supplement.jsonl','signature-supplement-summary.json')
METADATA_FORMS=('.ilean.hash','.olean.hash','.olean.server.hash','.olean.private.hash','.ir.sig.hash','.ir.hash','.trace')
ARCHIVES={str(Path('/workspace/toolchains/lean-4.34.0-linux/lib/lean')/n) for n in ['libInit.a','libLake.a','libLean.a','libLeanChecker.a','libLeanIR.a','libLeanc.a','libStd.a','libleancpp.a','libleanmanifest.a','libleanrt.a']}
QUALIFICATION='NEWLY_OBSERVED_LOCAL; neither historical preservation nor authenticated dependency provenance'
def inspect_metadata(path):
 p=Path(path)
 for parent in p.absolute().parents:require(not parent.is_symlink(),'Symlink input parent')
 s=p.lstat()
 require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'Nonregular/linked search input: '+str(p))
 return dict(path=str(p),bytes=s.st_size,identity=signature(s),mode=stat.S_IMODE(s.st_mode),uid=s.st_uid,link_count=s.st_nlink,metadata_only=True)
def walk_files(root):
 root=Path(root)
 for parent in root.absolute().parents:require(not parent.is_symlink(),'Symlink search parent')
 require(stat.S_ISDIR(root.lstat().st_mode),'Invalid search root')
 for p in root.rglob('*'):
  s=p.lstat()
  if stat.S_ISDIR(s.st_mode):continue
  yield p,inspect_metadata(p)
def family(path,suffix,roots,prior):
 p=Path(path);require(str(p).endswith(suffix),'Wrong family suffix')
 stem=str(p)[:-len(suffix)];olean=stem+'.olean'
 require(olean in prior,'Unbound module family: '+str(path))
 matches=[Path(r) for r in roots if p.is_relative_to(r)]
 require(len(matches)==1,'Ambiguous module search root')
 relative=Path(stem).relative_to(matches[0])
 return '.'.join(relative.parts),olean,stem+'.ir'
def metadata_form(path):
 return next((suffix for suffix in METADATA_FORMS if str(path).endswith(suffix)),None)
def load_prior():
 draft=ROOT/'checkpoints/light-eft-supplied-forest-draft-20261018'
 ref=json.loads((draft/'accepted-imports.json').read_text())['accepted_full_input_inventory']
 p=ROOT/ref['path'];bind(p,ref)
 rows=[json.loads(line) for line in p.read_text().splitlines()]
 require(len(rows)==len({r['path'] for r in rows}),'Duplicate prior inventory path')
 return {r['path']:r for r in rows},dict(path=str(p),**{k:ref[k] for k in ['bytes','sha256'] if k in ref})
def build_expected(spec,work,wrapper_commit):
 env=copy.deepcopy(spec['environment']);old=spec['future_work_root'];work=str(work)
 for k,v in env.items():env[k]=v.replace(old,work)
 env['LIGHTEFT_SOURCE_COMMIT']='40029953e9e53525f0f1f431d6d56333b05183a3'
 env['LIGHTEFT_HARNESS_COMMIT']=wrapper_commit
 plans=[]
 for item in spec['commands']:
  e=copy.deepcopy(env);e.update({k:v.replace(old,work) for k,v in item.get('environment_additions',{}).items()})
  for k in item.get('environment_remove',[]):e.pop(k,None)
  plans.append(dict(stage=item['stage'],module=TARGET,argv=[a.replace(old,work) for a in item['argv']],env=e,sources=item['submitted_sources']))
 return plans
def exact_commands(spec,work,wrapper_commit,plans):
 require(str(work)==spec['future_work_root'],'Work root differs from approved exact plan')
 require(plans==build_expected(spec,work,wrapper_commit),'Changed exact argv/environment')
 sysroot='/workspace/toolchains/lean-4.34.0-linux'
 require(spec['environment']['LEAN_SYSROOT']==sysroot and all(p['env']['LEAN_SYSROOT']==sysroot for p in plans),'Pinned LEAN_SYSROOT differs')
 require([p['stage'] for p in plans]==list(STAGES),'Changed four-stage schedule')
 require(all(p['argv'][0]==sysroot+'/bin/'+('leanchecker' if p['stage']=='replay' else 'lean') for p in plans),'Archive exclusion forbids linking/other tools')
class Inventory:
 def __init__(self,prior,signatures,policy,diagnosis,roots):
  self.prior=copy.deepcopy(prior);self.signatures={r['path']:copy.deepcopy(r) for r in signatures}
  require(len(self.signatures)==len(signatures),'Duplicate signature supplement')
  self.policy=copy.deepcopy(policy);self.roots=list(map(Path,roots))
  self.archives=set(policy['exact_static_archives']);self.excluded=set()
  require(self.archives==ARCHIVES,'Not the ten exact scoped archives')
  for row in diagnosis:
   p=row['path']
   if p in self.prior:continue  # Never downgrade any previously bound input.
   if not any(Path(p).is_relative_to(r) for r in self.roots):continue
   if p.endswith('.ir.sig'):continue
   if p in self.archives:self.excluded.add(p);continue
   suffix=metadata_form(p);require(suffix is not None,'Unknown diagnosed exclusion')
   family(p,suffix,self.roots,self.prior)
   self.excluded.add(p)
  require({p for p in self.archives if any(Path(p).is_relative_to(r) for r in self.roots)}<=self.excluded|set(self.prior),'Missing exact archive in diagnosis')
  for path,row in self.signatures.items():
   require(path not in self.prior,'Signature would replace an old binding')
   module,olean,ir=family(path,'.ir.sig',self.roots,self.prior)
   require(ir in self.prior,'Signature has no old bound IR family')
   require(row['module']==module and row['family']=={'olean':{'path':olean,'sha256':self.prior[olean]['sha256']},'ir':{'path':ir,'sha256':self.prior[ir]['sha256']}},'Signature module-family association differs')
   require(row['qualification']==QUALIFICATION,'Signature qualification omitted')
  self.old_paths={p for p in self.prior if any(Path(p).is_relative_to(r) for r in self.roots)}
 def scan(self):
  semantic={};excluded={};sigs=set();seen=set();per_root={}
  for root in self.roots:
   found=set()
   for p,meta in walk_files(root):
    path=str(p);require(path not in seen,'Duplicate physical search path');seen.add(path);found.add(path)
    if path in self.prior:semantic[path]=bind(p,self.prior[path])
    elif path.endswith('.ir.sig'):
     require(path in self.signatures,'New/unreviewed signature: '+path)
     expected=self.signatures[path];actual=bind(p,expected)
     require(actual['identity']==expected['identity'],'Signature identity changed: '+path)
     semantic[path]=actual;sigs.add(path)
    elif path in self.excluded:
     require(path in self.archives or metadata_form(path) is not None,'Unknown exclusion')
     excluded[path]=meta
    else:raise Rejected('Unknown search input: '+path)
   per_root[str(root)]=found
  require(sigs==set(self.signatures),'Missing/new signature supplement membership')
  require(self.old_paths<=seen,'Missing old bound semantic input')
  require(set(excluded)==self.excluded,'Excluded-file membership changed')
  return dict(semantic=semantic,excluded=excluded,members=per_root,
   old_semantic_count=len(self.old_paths),signature_count=len(sigs),excluded_count=len(excluded))
def load_inventory(commit,plans,work,roots):
 from scope import reviewed_inputs
 spec,_,_=reviewed_inputs();exact_commands(spec,work,commit,plans)
 require(list(map(str,roots))==plans[0]['env']['LEAN_PATH'].split(':')[1:],'Changed semantic search roots')
 protected={};raw={}
 for name in DATA:
  p=HERE/name;blob=subprocess.check_output(['git','show',commit+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  row,body=regular(p);require(body==blob,'Unreviewed inventory/supplement data');protected[str(p)]=row;raw[name]=body
 policy=json.loads(raw['inventory-policy.json']);summary=json.loads(raw['signature-supplement-summary.json'])
 require(summary['qualification']==QUALIFICATION,'Local signature qualifier differs')
 sigbytes=raw['signature-supplement.jsonl']
 require(sha(sigbytes)==summary['sha256'] and len(sigbytes)==summary['bytes'],'Signature supplement digest differs')
 signatures=[json.loads(line) for line in sigbytes.splitlines()]
 require(len(signatures)==summary['signatures'] and sum(r['bytes'] for r in signatures)==summary['signature_payload_bytes'],'Signature supplement count/size differs')
 diag=ROOT/policy['diagnosis']['path'];b=diag.read_bytes()
 require(sha(b)==policy['diagnosis']['sha256'],'Diagnosed exclusion authority changed')
 protected[str(diag)]=bind(diag,policy['diagnosis'])
 prior,ref=load_prior()
 inv=Inventory(prior,signatures,policy,[json.loads(line) for line in b.splitlines()],roots)
 return inv,protected,dict(summary=summary,supplement=protected[str(HERE/'signature-supplement.jsonl')],policy=protected[str(HERE/'inventory-policy.json')],qualification=QUALIFICATION)
def capture_signatures(prior,roots):
 rows=[]
 for root in map(Path,roots):
  for p,meta in walk_files(root):
   if not str(p).endswith('.ir.sig'):continue
   module,olean,ir=family(p,'.ir.sig',roots,prior);require(ir in prior,'Unbound IR for signature capture')
   row=bind(p);row.update(module=module,family={'olean':{'path':olean,'sha256':prior[olean]['sha256']},'ir':{'path':ir,'sha256':prior[ir]['sha256']}},qualification=QUALIFICATION)
   require(str(p) not in prior,'Do not overwrite historical signature binding');rows.append(row)
 return sorted(rows,key=lambda r:r['path'])
