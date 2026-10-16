"""New semantic proof against hash-bound pre-pilot objects; not a repaired-source clean gate."""
from pathlib import Path
import json,hashlib,os,subprocess,datetime,shutil
from SequentialLean import run_locked
from MemoryAdmission import admit_memory
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence';TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
h=lambda b:hashlib.sha256(b).hexdigest();old=ROOT/'checkpoints/light-eft-weight-value-pilot-20261016/evidence/fresh-build-state.json';state=json.loads(old.read_text())
source=ROOT/'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/StoredOriginalWeightEncoding.lean';before=E/'StoredOriginalWeightEncoding.before.lean.txt';proof=B/'LegacyEquivalence.lean'
assert before.read_bytes()==subprocess.check_output(['git','show','23c20b1c58bb24bc53419819ae755f82b7f71cd8:'+str(source.relative_to(ROOT))],cwd=ROOT)
assert h(before.read_bytes())==state['LightEFTSpanners.StoredOriginalWeightEncoding']['inputs']['source_sha256']
bodies=json.loads((E/'replacement-bodies.json').read_text())
for body in bodies.values():assert body in source.read_text() and body in proof.read_text()
body='\n'.join(bodies.values())
legacy=[]
for n,r in state.items():
 p=ROOT/'.lake/weight-value-pilot/lib/lean'/Path(*n.split('.')).with_suffix('.olean');assert h(p.read_bytes())==r['object_sha256'];legacy.append(dict(module=n,object=str(p),sha256=r['object_sha256']))
(E/'legacy-comparison-inputs.json').write_text(json.dumps(dict(legacy_source='23c20b1c58bb24bc53419819ae755f82b7f71cd8',before_sha256=h(before.read_bytes()),replacement_sha256=h(source.read_bytes()),replacement_body_sha256=h(body.encode()),legacy_objects=legacy,scope='Fresh full-list equality proof against preserved old implementation; audit uses isolated outputs with separately recorded byte-identical inherited imports'),indent=2)+'\n')
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
for pin in pins:assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/pin['name'],text=True).strip()==pin['rev']
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH'];os.environ['LEAN_SYSROOT']=str(TOOL)
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[ROOT/'.lake/weight-value-pilot/lib/lean']+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
out=ROOT/'.lake/weight-typed-pilot-comparison/LegacyEquivalence.olean';out.parent.mkdir(parents=True,exist_ok=True)
admit_memory(E,'legacy-semantic-equivalence')
raw=run_locked('legacy-semantic-equivalence',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(B),'-o',str(out),str(proof)],ROOT,E,env=os.environ.copy(),submitted_sources=[proof,before,source])
(E/'legacy-equivalence-object.json').write_text(json.dumps(dict(path=str(out),sha256=h(out.read_bytes()),bytes=out.stat().st_size),indent=2)+'\n');print(raw)
