"""New semantic proof against hash-bound pre-pilot objects; not a repaired-source clean gate."""
from pathlib import Path
import json,hashlib,os,subprocess,datetime,shutil
from SequentialLean import run_locked
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence';TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
h=lambda b:hashlib.sha256(b).hexdigest();old=ROOT/'checkpoints/light-eft-strict-aggregate-20261016/evidence/build-state.json';state=json.loads(old.read_text())
source=ROOT/'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/ControllerTrace.lean';before=E/'ControllerTrace.before.lean.txt';proof=B/'LegacyEquivalence.lean'
assert before.read_bytes()==subprocess.check_output(['git','show','e9d3f5ca8fe07062976d1681f8ad24294df6bb10:'+str(source.relative_to(ROOT))],cwd=ROOT)
assert h(before.read_bytes())==state['LightEFTSpanners.ControllerTrace']['inputs']['source_sha256']
body='  Nat.rec (motive := fun _ => S → S) (fun s => s)\n    (fun _ previous s => match step s with | none => s | some t => previous t)'
assert body in source.read_text() and body in proof.read_text()
legacy=[]
for n,r in state.items():
 p=ROOT/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean');assert h(p.read_bytes())==r['object_sha256'];legacy.append(dict(module=n,object=str(p),sha256=r['object_sha256']))
(E/'legacy-comparison-inputs.json').write_text(json.dumps(dict(legacy_source='e9d3f5ca8fe07062976d1681f8ad24294df6bb10',before_sha256=h(before.read_bytes()),replacement_sha256=h(source.read_bytes()),replacement_body_sha256=h(body.encode()),legacy_objects=legacy,scope='Fresh equality proof only; old objects not used for the fresh project audit'),indent=2)+'\n')
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
for pin in pins:assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/pin['name'],text=True).strip()==pin['rev']
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH'];os.environ['LEAN_SYSROOT']=str(TOOL)
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[ROOT/'.lake/build/lib/lean']+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
ps=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
assert not any(x.split()[-1] in ['lean','lake','leanchecker'] and 'Z' not in x.split()[2] for x in ps.splitlines()[1:])
assert shutil.disk_usage(ROOT).free>2*1024**3
out=ROOT/'.lake/controller-pilot-comparison/LegacyEquivalence.olean';out.parent.mkdir(parents=True,exist_ok=True)
raw=run_locked('legacy-semantic-equivalence',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(B),'-o',str(out),str(proof)],ROOT,E,env=os.environ.copy(),submitted_sources=[proof,before,source])
(E/'legacy-equivalence-object.json').write_text(json.dumps(dict(path=str(out),sha256=h(out.read_bytes()),bytes=out.stat().st_size),indent=2)+'\n');print(raw)
