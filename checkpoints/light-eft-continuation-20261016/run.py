from pathlib import Path
import os,sys,re,json,tomllib,hashlib,subprocess
from SequentialLean import run_locked
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
assert len(pins)==9
for p in pins:
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/p['name'],text=True).strip()==p['rev']
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[ROOT/'.lake/build/lib/lean']+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
mods={}
for lib in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']:
 base=ROOT/lib['srcDir']
 for p in base.rglob('*.lean'):
  if 'verification' not in p.relative_to(base).parts:mods['.'.join(p.relative_to(base).with_suffix('').parts)]=(p,base)
def run(label,args,src=None):
 r=run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=src);print(label,'PASS',flush=True);return r
name='LightEFTSpanners.BlowupCertificateThreshold';mode=sys.argv[1]
if mode=='dependencies':
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  for m in re.findall(r'^import\s+([\w.]+)',mods[n][0].read_text(),re.M):
   if m in mods:visit(m)
  order.append(n)
 visit(name)
 (E/'dependency-order.json').write_text(json.dumps(order,indent=2)+'\n')
 run('official-version',[str(TOOL/'bin/lean'),'--version'],[ROOT/'lean-toolchain'])
 for n in order[:-1]:
  src,base=mods[n];out=ROOT/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  run('compile-'+n,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','--root='+str(base),'-o',str(out),str(src)])
elif mode=='restore':
 src,base=mods['LightEFTSpanners.LargeCloudCertificate'];out=ROOT/'.lake/build/lib/lean/LightEFTSpanners/LargeCloudCertificate.olean'
 run('restore-LargeCloudCertificate',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(base),'-o',str(out),str(src)])
elif mode=='compile':
 src,base=mods[name];out=ROOT/'.lake/build/lib/lean'/Path(*name.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 run('compile-'+name,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(base),'-o',str(out),str(src)])
elif mode=='replay':
 for n in json.loads((E/'dependency-order.json').read_text()):
  raw=run('replay-'+n,[str(TOOL/'bin/leanchecker'),'-v',n],[mods[n][0]]);assert raw.strip()=='replaying '+n
elif mode=='audit':
 print(run('recursive-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'RecursiveAudit.lean')]))
