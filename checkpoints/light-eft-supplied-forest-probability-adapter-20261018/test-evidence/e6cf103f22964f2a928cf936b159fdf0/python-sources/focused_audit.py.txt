"""New-module inventory and exact reachable closure; no full-graph reconciler."""
from pathlib import Path
import collections,hashlib,json,re
from contracts import *
ALLOWED={'propext','Classical.choice','Quot.sound'}
KINDS={'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}
def table(path,header):
 _,b=regular(path);require(b.endswith(b'\n'),'Truncated table')
 lines=b.decode().splitlines();require(lines and lines[0].split('\t')==header,'Wrong table header')
 rows=[]
 for l in lines[1:]:
  values=l.split('\t');require(len(values)==len(header),'Malformed table row');rows.append(dict(zip(header,values)))
 return rows
def validate(ci,expected_imports,raw):
 ci=Path(ci);outputs(ci,True)
 require(len(expected_imports)==len(set(expected_imports))==213,'Audit requires exactly 213 dependency names')
 require(collections.Counter(m.split('.')[0] for m in expected_imports)=={'LightEFTSpanners':156,'LightSpanners':56,'LightEFTSuppliedForestStage':1},'Audit dependency prefixes differ')
 _,b=regular(ci/'import-closure-loaded.txt');require(b.endswith(b'\n'),'Truncated imports')
 loaded=b.decode().splitlines()
 require(loaded and all(loaded) and len(loaded)==len(set(loaded)),'Empty/duplicate imports')
 require({m for m in loaded if project(m)}==set(expected_imports)|{TARGET},'Exact project imports differ')
 require((ci/'strict-violations.txt').read_bytes()==b'\n','Nonempty/malformed strict findings')
 invrows=table(ci/'actual-owner-inventory.tsv',['owner','name','kind','unsafe','partial'])
 deprows=table(ci/'recursive-dependencies.tsv',['name','owner','kind','typeDependencies','bodyDependencies','unsafe','partial'])
 inv={r['name']:r for r in invrows};dep={r['name']:r for r in deprows}
 require(inv and len(inv)==len(invrows) and len(dep)==len(deprows),'Empty/duplicate roots/closure')
 require(THEOREM in inv and inv[THEOREM]['kind']=='theorem','Named theorem absent/wrong kind')
 for r in invrows+deprows:
  require(r['name'] and r['kind'] in KINDS,'Invalid declaration kind/name')
  require(r['unsafe']=='false' and r['partial']=='false','Unsafe/partial declaration')
  require(r['owner'] in loaded or r['owner']=='[anonymous]','Owner not loaded')
 for n,r in inv.items():
  require(r['owner']==TARGET and r['kind']!='axiom','Wrong new-module owner/project axiom')
  require(n in dep and all(dep[n][k]==r[k] for k in ['owner','kind','unsafe','partial']),'Root/closure metadata differs')
 require({n for n,r in dep.items() if r['owner']==TARGET}==set(inv),'Omitted new-module private/generated root')
 axioms={n for n,r in dep.items() if r['kind']=='axiom'}
 require(axioms<=ALLOWED,'Disallowed recursive axiom')
 require(all(not project(r['owner']) or r['kind']!='axiom' for r in deprows),'Imported project axiom')
 links={}
 for n,r in dep.items():
  names=[]
  for col in ['typeDependencies','bodyDependencies']:
   if r[col]:
    part=r[col].split(',');require(all(part),'Empty dependency name');names+=part
  require(set(names)<=set(dep),'Dangling type/body dependency')
  if r['kind'] in {'inductive','constructor','recursor'}:require(bool(r['bodyDependencies']),'Missing inductive/constructor/recursor links')
  links[n]=list(dict.fromkeys(names))  # Raw exporter rows remain unchanged.
 seen=set();todo=list(inv)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo+=links[n]
 require(seen==set(dep),'Closure not exactly reachable from new-module roots')
 from probability_plan import REQUIRED_INTERFACES
 for interface in REQUIRED_INTERFACES:require(interface in seen,'Missing required reachable interface: '+interface)
 summaries=re.findall(r'PASS: (\d+) new-module actual-owner declarations; (\d+) recursive constants, (\d+) opaque bodies; axioms #?\[([^\]]*)\]',raw,re.S)
 require(len(summaries)==1,'Missing/duplicate audit summary')
 a,b,c,ax=summaries[0]
 counts=(len(inv),len(dep),sum(r['kind']=='opaque' for r in deprows))
 require(tuple(map(int,[a,b,c]))==counts,'Audit counts differ from exports')
 require({x.strip() for x in ax.split(',') if x.strip()}==axioms,'Printed axioms differ')
 require(not warning_lines(raw),'Actual Lean warning/error diagnostic')
 return dict(new_owner_roots=counts[0],recursive_constants=counts[1],opaque_bodies=counts[2],
  axioms=sorted(axioms),project_imports=sorted(set(expected_imports)|{TARGET}),
  strict_findings=0,recursive_types_and_bodies=True)
def chunk(source,directory,target=200000):
 source=Path(source);directory=Path(directory);directory.mkdir(parents=True,exist_ok=False)
 before=bind(source);parts=[];buf=bytearray()
 def flush():
  if not buf:return
  name='part-%04d.txt'%len(parts);(directory/name).write_bytes(buf)
  parts.append(dict(path=name,bytes=len(buf),sha256=sha(buf)));buf.clear()
 with source.open('rb') as f:
  for row in f:
   if buf and len(buf)+len(row)>target:flush()
   buf.extend(row)
 flush()
 require(bind(source)==before,'Source changed during chunk export')
 m=dict(source=str(source),bytes=before['bytes'],sha256=before['sha256'],row_aligned=True,target_bytes=target,parts=parts)
 save(directory/'manifest.json',m);verify_chunks(directory,source);return m
def verify_chunks(directory,source):
 directory=Path(directory);_,b=regular(directory/'manifest.json');m=json.loads(b)
 require(m['source']==str(source) and m.get('row_aligned') is True and isinstance(m.get('target_bytes'),int) and m['target_bytes']>0,'Chunk source/row contract differs')
 require(set(p.name for p in directory.iterdir())=={'manifest.json'}|{r['path'] for r in m['parts']},'Unexpected/missing chunk files')
 h=hashlib.sha256();size=0
 for i,r in enumerate(m['parts']):
  require(r['path']=='part-%04d.txt'%i,'Chunk order/path/sequence differs')
  row,b=regular(directory/r['path']);require(row['bytes']==r['bytes'] and row['sha256']==r['sha256'],'Chunk hash/size differs')
  require(bool(b),'Empty chunk')
  if i+1<len(m['parts']):require(b.endswith(b'\n'),'Chunk boundary splits a row')
  h.update(b);size+=len(b)
 original=bind(source)
 require(size==m['bytes']==original['bytes'] and h.hexdigest()==m['sha256']==original['sha256'],'Incomplete chunk reconstruction')
 return m
def export_all(ci,raw,directory):
 directory=Path(directory);directory.mkdir(exist_ok=False)
 names=[(str(n),Path(ci)/n) for n in EXPORTS]+[('raw.log',Path(raw))]
 manifests={n:chunk(src,directory/n) for n,src in names}
 require(set(manifests)==set(EXPORTS)|{'raw.log'},'Incomplete five-file export')
 for n,src in names:verify_chunks(directory/n,src)
 return manifests
