from pathlib import Path
import os,sys,json,subprocess
from SequentialLean import run_locked
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
for p in pins:
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/p['name'],text=True).strip()==p['rev']
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[ROOT/'.lake/build/lib/lean']+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
name='LightEFTSpanners.NativeWeightedFaults';base=ROOT/'Light Edge Fault Tolerant Graph Spanners'
src=base/'LightEFTSpanners/NativeWeightedFaults.lean';mode=sys.argv[1]
def run(label,args,sources):
 raw=run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=sources)
 print(label,'PASS',flush=True);return raw
if mode=='version':
 print(run('official-version',[str(TOOL/'bin/lean'),'--version'],[ROOT/'lean-toolchain']))
elif mode=='compile':
 out=ROOT/'.lake/build/lib/lean/LightEFTSpanners/NativeWeightedFaults.olean';out.parent.mkdir(parents=True,exist_ok=True)
 print(run('compile-'+name,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(base),'-o',str(out),str(src)],[src]))
elif mode=='replay':
 raw=run('replay-'+name,[str(TOOL/'bin/leanchecker'),'-v',name],[src]);assert raw.strip()=='replaying '+name
elif mode=='audit':
 print(run('recursive-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'RecursiveAudit.lean')],[B/'RecursiveAudit.lean']))
else:raise ValueError(mode)
