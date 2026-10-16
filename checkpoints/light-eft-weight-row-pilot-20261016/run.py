from pathlib import Path
import os,sys,json,subprocess,hashlib,shutil,datetime
from SequentialLean import run_locked
from MemoryAdmission import admit_memory
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
OUT=ROOT/'.lake/weight-row-pilot/lib/lean'
h=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
for pin in pins:assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/pin['name'],text=True).strip()==pin['rev']
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH'];os.environ['LEAN_SYSROOT']=str(TOOL)
rows=json.loads((E/'source-graph.json').read_text());mods={r['module']:r for r in rows}
def envpath(first):os.environ['LEAN_PATH']=os.pathsep.join(map(str,first+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
def run(label,args,sources):
 admit_memory(E,label)
 raw=run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=sources)
 print(label,'PASS',flush=True);return raw
mode=sys.argv[1]
if mode in ['pilot','build']:
 envpath([OUT]);statefile=E/'fresh-build-state.json';state=json.loads(statefile.read_text()) if statefile.exists() else {}
 for r in rows:
  n=r['module'];p=ROOT/r['path'];deps=[d for line in p.read_text().splitlines() if line.startswith('import ') for d in line[7:].split('--',1)[0].split() if d in mods]
  inputs=dict(source_sha256=h(p.read_bytes()),imports={d:h((OUT/Path(*d.split('.')).with_suffix('.olean')).read_bytes()) for d in deps})
  out=OUT/Path(*n.split('.')).with_suffix('.olean')
  if n in state and state[n]['inputs']==inputs and out.exists() and h(out.read_bytes())==state[n]['object_sha256']:
   if mode=='pilot' and n=='LightEFTSpanners.StoredOriginalWeightMatrix':
    print(run('pilot-semantics-and-safety',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'PilotCheck.lean')],[B/'PilotCheck.lean',p]))
    break
   continue
  out.parent.mkdir(parents=True,exist_ok=True)
  run('fresh-compile-'+n,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(ROOT/r['srcDir']),'-o',str(out),str(p)],[p])
  state[n]=dict(inputs=inputs,object_sha256=h(out.read_bytes()));statefile.write_text(json.dumps(state,indent=2)+'\n')
  if mode=='pilot' and n=='LightEFTSpanners.StoredOriginalWeightMatrix':
   print(run('pilot-semantics-and-safety',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'PilotCheck.lean')],[B/'PilotCheck.lean',p]))
   break
elif mode in ['audit','replay','fresh-pilot-check','refuse-aggregate']:
 envpath([OUT]);state=json.loads((E/'fresh-build-state.json').read_text());assert len(state)==486
 for r in rows:
  assert h((ROOT/r['path']).read_bytes())==state[r['module']]['inputs']['source_sha256']
  assert h((OUT/Path(*r['module'].split('.')).with_suffix('.olean')).read_bytes())==state[r['module']]['object_sha256']
 if mode=='audit':
  print(run('complete-all-owner-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'CompleteAudit.lean')],[B/'CompleteAudit.lean']+[ROOT/r['path'] for r in rows]))
 elif mode=='refuse-aggregate':
  os.environ['LIGHTEFT_CHECKER_TARGET']='LightEFTSpanners'
  os.environ['LIGHTEFT_CHECKER_RESOLUTION_FILE']=str(E/'aggregate-target-refusal.json')
  print(run('aggregate-target-preflight-refusal',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'ResolveCheckerTarget.lean')],[B/'ResolveCheckerTarget.lean']))
 elif mode=='fresh-pilot-check':
  print(run('fresh-pilot-semantics-and-safety',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'PilotCheck.lean')],[B/'PilotCheck.lean',ROOT/mods['LightEFTSpanners.StoredOriginalWeightMatrix']['path']]))
 else:
  n='LightEFTSpanners.StoredOriginalWeightMatrix';os.environ['LIGHTEFT_CHECKER_TARGET']=n
  os.environ['LIGHTEFT_CHECKER_RESOLUTION_FILE']=str(E/'pilot-target-resolution.json')
  print(run('official-target-resolution',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'ResolveCheckerTarget.lean')],[B/'ResolveCheckerTarget.lean',ROOT/mods[n]['path']]))
  raw=run('singleton-pilot-replay',[str(TOOL/'bin/leanchecker'),'-v',n],[ROOT/mods[n]['path']]);assert raw.strip()=='replaying '+n
else:raise ValueError(mode)
