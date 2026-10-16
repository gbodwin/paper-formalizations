from pathlib import Path
import os,sys,json,subprocess,hashlib,shutil,datetime
from SequentialLean import run_locked
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux');PKG=Path('/workspace/paper-formalizations/.lake/packages')
h=lambda data:hashlib.sha256(data).hexdigest()
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
for p in pins:assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PKG/p['name'],text=True).strip()==p['rev']
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
os.environ['LEAN_PATH']=os.pathsep.join(map(str,[ROOT/'.lake/build/lib/lean']+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
rows=json.loads((E/'source-graph.json').read_text());mods={r['module']:r for r in rows}
statefile=E/'build-state.json';state=json.loads(statefile.read_text()) if statefile.exists() else {}
def obj(n):return ROOT/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean')
def inputs(n):
 r=mods[n];s=ROOT/r['path'];deps=[]
 for line in s.read_text().splitlines():
  if line.startswith('import '):deps.extend(d for d in line[7:].split() if d in mods)
 return dict(source_sha256=h(s.read_bytes()),imports={d:h(obj(d).read_bytes()) for d in deps})
def run(label,args,sources):
 ps=subprocess.check_output(['ps','-eo','pid,stat,comm'],text=True)
 assert not any(row.split()[-1] in ['lean','lake','leanchecker'] and 'Z' not in row.split()[1] for row in ps.splitlines()[1:])
 assert shutil.disk_usage(ROOT).free>2*1024**3
 with (E/'invocation-preflights.jsonl').open('a') as f:f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),label=label,processes=ps,free_disk=shutil.disk_usage(ROOT).free,meminfo=Path('/proc/meminfo').read_text(),memory_limit=Path('/sys/fs/cgroup/memory.max').read_text().strip()))+'\n')
 raw=run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=sources)
 print(label,'PASS',flush=True);return raw
mode=sys.argv[1]
if mode=='build':
 for r in rows:
  n=r['module'];current=inputs(n);out=obj(n)
  if n in state and state[n]['inputs']==current and out.exists() and h(out.read_bytes())==state[n]['object_sha256']:continue
  out.parent.mkdir(parents=True,exist_ok=True)
  run('compile-'+n,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(ROOT/r['srcDir']),'-o',str(out),str(ROOT/r['path'])],[ROOT/r['path']])
  state[n]=dict(inputs=current,object_sha256=h(out.read_bytes()));statefile.write_text(json.dumps(state,indent=2)+'\n')
elif mode=='replay':
 for r in rows:
  n=r['module']
  if n=='LightEFTSpanners':continue # official checker prefix expands; aggregate is import-only
  assert state[n]['inputs']==inputs(n) and state[n]['object_sha256']==h(obj(n).read_bytes())
  raw=run('replay-'+n,[str(TOOL/'bin/leanchecker'),'-v',n],[ROOT/r['path']]);assert raw.strip()=='replaying '+n
elif mode=='diagnostic-audit':
 print(run('diagnostic-recursive-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'DiagnosticAudit.lean')],[B/'DiagnosticAudit.lean']+[ROOT/r['path'] for r in rows]))
elif mode=='audit':
 print(run('full-recursive-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(B/'FullAudit.lean')],[B/'FullAudit.lean']+[ROOT/r['path'] for r in rows]))
else:raise ValueError(mode)
