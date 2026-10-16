from pathlib import Path
import sys,os,json,hashlib
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
from SequentialLean import run_locked
E=Path(__file__).resolve().parent/'evidence'
old=json.loads((ROOT/'checkpoints/directed-preservers-20261016/evidence/attempt-013.json').read_text())
env=os.environ.copy();env['LEAN_PATH']=old['LEAN_PATH']
env['PATH']='/workspace/toolchains/lean-4.34.0-linux/bin:'+env['PATH']
name=sys.argv[1];mode=sys.argv[2] if len(sys.argv)>2 else 'compile'
module='SlackSparsification.'+name
src=ROOT/'A Note on Distance-Preserving Graph Sparsification'/Path(*module.split('.')).with_suffix('.lean')
if mode=='audit':
 src=ROOT/'A Note on Distance-Preserving Graph Sparsification/verification/SCCInternalAudit.lean'
 cmd=['/workspace/toolchains/lean-4.34.0-linux/bin/lean','-j1','-DautoImplicit=false','-DwarningAsError=true',str(src)]
elif mode=='compile':
 cmd=['/workspace/toolchains/lean-4.34.0-linux/bin/lean','-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(src.parents[1]),'-o',str(ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')),str(src)]
else:cmd=['/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker','-v',module]
# Snapshot every submitted source; failed attempts remain inspectable after edits.
h=hashlib.sha256(src.read_bytes()).hexdigest();(E/'sources').mkdir(parents=True,exist_ok=True)
(E/'sources'/(h+'.lean')).write_bytes(src.read_bytes())
print(run_locked(mode+'-'+name,cmd,ROOT,E,env=env,submitted_sources=[src]))
