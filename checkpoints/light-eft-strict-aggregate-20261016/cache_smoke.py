"""Validate the clean gate's official cache CLI bootstrap method, sequentially."""
from pathlib import Path
import os,json,re,tempfile,sys,subprocess,shutil
from SequentialLean import run_locked
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
bootstrap=Path(tempfile.mkdtemp(prefix='light-eft-cache-bootstrap-'))
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[bootstrap,TOOL/'lib/lean']))
os.environ['LEAN_SRC_PATH']=os.pathsep.join(map(str,[ROOT]+[PKG/p['name'] for p in pins]))
pattern=re.compile(r'^(?:(?:public|private|meta)\s+)*import\s+(.+)$',re.M)
seen=set();order=[]
def visit(n):
 if n in seen:return
 seen.add(n)
 for pin in pins:
  base=PKG/pin['name'];p=base/Path(*n.split('.')).with_suffix('.lean')
  if p.exists():
   for group in pattern.findall(p.read_text()):
    for dep in group.split('--',1)[0].split():visit(dep)
   order.append((n,p,base));return
visit('Cache.Main')
def run(label,args,src):
 ps=subprocess.check_output(['ps','-eo','pid,stat,comm'],text=True)
 assert not any(x.split()[-1] in ['lean','lake','leanchecker'] and 'Z' not in x.split()[1] for x in ps.splitlines()[1:])
 print(run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=src),flush=True)
for n,p,base in order:
 out=bootstrap/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 run('cache-bootstrap-smoke-'+n,[str(TOOL/'bin/lean'),'-j1','--root='+str(base),'-o',str(out),str(p)],[p])
run('official-cache-help-smoke',[str(TOOL/'bin/lean'),'-j1','--run',str(PKG/'mathlib/Cache/Main.lean'),'--help'],[p for _,p,_ in order])
print('PASS: unmodified official cache helper bootstrap and interpreter help; network retrieval reserved for clean CI')
