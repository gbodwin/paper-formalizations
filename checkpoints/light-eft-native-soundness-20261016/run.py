from pathlib import Path
import os,sys,json,subprocess,shutil,datetime
from SequentialLean import run_locked
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
for p in pins:
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/p['name'],text=True).strip()==p['rev']
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[ROOT/'.lake/build/lib/lean']+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
leaf=sys.argv[2] if len(sys.argv)>2 else 'NativeGreedySoundness'
name='LightEFTSpanners.'+leaf;base=ROOT/'Light Edge Fault Tolerant Graph Spanners'
src=base/'LightEFTSpanners'/(leaf+'.lean');mode=sys.argv[1]
def run(label,args,sources):
 ps=subprocess.check_output(['ps','-eo','pid,stat,comm'],text=True)
 assert not any(row.split()[-1] in ['lean','lake','leanchecker'] and 'Z' not in row.split()[1] for row in ps.splitlines()[1:])
 assert shutil.disk_usage(ROOT).free>2*1024**3
 with (E/'invocation-preflights.jsonl').open('a') as out:out.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),label=label,processes=ps,free_disk=shutil.disk_usage(ROOT).free,memory_limit=Path('/sys/fs/cgroup/memory.max').read_text().strip()))+'\n')
 raw=run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=sources)
 print(label,'PASS',flush=True);return raw
if mode=='dependencies':
 import re,tomllib
 mods={}
 for lib in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']:
  libbase=ROOT/lib['srcDir']
  for p in libbase.rglob('*.lean'):
   if 'verification' not in p.relative_to(libbase).parts:mods['.'.join(p.relative_to(libbase).with_suffix('').parts)]=(p,libbase)
 for n in json.loads((E/'dependency-order.json').read_text()):
  p,libbase=mods[n];out=ROOT/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  run('dependency-'+n,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','--root='+str(libbase),'-o',str(out),str(p)],[p])
elif mode=='version':
 print(run('official-version',[str(TOOL/'bin/lean'),'--version'],[ROOT/'lean-toolchain']))
elif mode=='compile':
 out=ROOT/'.lake/build/lib/lean/LightEFTSpanners'/(leaf+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 print(run('compile-'+name,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(base),'-o',str(out),str(src)],[src]))
elif mode=='replay':
 raw=run('replay-'+name,[str(TOOL/'bin/leanchecker'),'-v',name],[src]);assert raw.strip()=='replaying '+name
elif mode=='audit':
 print(run('recursive-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'RecursiveAudit.lean')],[B/'RecursiveAudit.lean']+[base/'LightEFTSpanners'/(n+'.lean') for n in ['NativeGreedySoundness', 'NativeCompleteInput', 'NativeMinimumOutput']]))
else:raise ValueError(mode)
