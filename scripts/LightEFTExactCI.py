"""Clean exact-source LightEFT-only gate. All Lean processes run sequentially under one lock."""
from pathlib import Path
import os,sys,json,subprocess,hashlib,shutil,re,traceback,datetime,urllib.request,tomllib
from LightEFTSequential import run_locked
ROOT=Path.cwd();E=ROOT/'ci-evidence';E.mkdir(exist_ok=True)
SOURCE=sys.argv[1];TOOL=Path(sys.argv[2]).resolve();PKG=ROOT/'.lake/packages'
h=lambda d:hashlib.sha256(d).hexdigest()
def save(n,x):
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def git(*args,cwd=ROOT):return subprocess.check_output(['git',*args],cwd=cwd,text=True).strip()
def capture(label,args,cwd=ROOT):
 p=subprocess.run(args,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(label+'.log')).write_text(p.stdout)
 if p.returncode:raise RuntimeError(label+' failed; see log')
 return p.stdout
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
assert len(pins)==9
assert h((ROOT/'lake-manifest.json').read_bytes())=='615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f'
assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.0'
assert git('rev-parse','HEAD')==SOURCE
assert not git('status','--porcelain','--untracked-files=no')
os.environ['PATH']=str(TOOL/'bin')+os.pathsep+os.environ['PATH']
records=[]
def run(label,args,sources):
 ps=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
 assert not any(x.split()[-1] in ['lean','lake','leanchecker'] and 'Z' not in x.split()[2] for x in ps.splitlines()[1:])
 assert shutil.disk_usage(ROOT).free>1024**3
 with (E/'preflights.jsonl').open('a') as f:f.write(json.dumps(dict(label=label,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),processes=ps,disk=shutil.disk_usage(ROOT).free,meminfo=Path('/proc/meminfo').read_text()))+'\n')
 raw=run_locked(label,args,ROOT,E,env=os.environ.copy(),submitted_sources=sources)
 records.append(label);print('PASS',label,flush=True);return raw
pattern=re.compile(r'^(?:(?:public|private|meta)\s+)*import\s+(.+)$',re.M)
def imports(p):return [n for group in pattern.findall(p.read_text()) for n in group.split('--',1)[0].split()]
def finalize():
 rs=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
 assert len({r['attempt_id'] for r in rs})==len(rs)
 assert len({(r['lock_device'],r['lock_inode']) for r in rs})<=1
 assert all(r['child_reaped'] for r in rs)
 assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(rs,rs[1:]))
 for r in rs:
  for s in r['submitted_sources']:
   data=(E/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes()
   assert len(data)==s['bytes'] and h(data)==s['sha256'] and data==Path(s['path']).read_bytes()
 save('execution-reconciliation.json',dict(source=SOURCE,attempts=len(rs),failed=[r['label'] for r in rs if r['exit']],unique_ids=True,one_lock_inode=True,nonoverlap=True,children_reaped=True,source_snapshots_verified=True))
 dep=E/'recursive-dependencies.tsv'
 if dep.exists():
  a=E/'audit-export';a.mkdir(exist_ok=True);parts=[];buf=b''
  def emit(data):
   p=a/('part-%03d.tsv'%len(parts));p.write_bytes(data);parts.append(dict(path=p.name,bytes=len(data),sha256=h(data)))
  raw=dep.read_bytes()
  for line in raw.splitlines(keepends=True):
   if buf and len(buf)+len(line)>200000:emit(buf);buf=b''
   buf+=line
  if buf:emit(buf)
  save('audit-export/manifest.json',dict(source='recursive-dependencies.tsv',bytes=len(raw),sha256=h(raw),parts=parts,reconstruction='Concatenate listed part bytes in order without separators.'))
 rows=[]
 for p in sorted(E.rglob('*')):
  if p.is_file() and p.name!='evidence-sha256.json':
   data=p.read_bytes();rows.append(dict(path=str(p.relative_to(E)),bytes=len(data),sha256=h(data)))
 save('evidence-sha256.json',rows)
try:
 # Read-only public API preflight. No credential injection or workflow API trigger.
 ci=[]
 for status in ['in_progress','queued','waiting','pending','requested']:
  url='https://api.github.com/repos/gbodwin/paper-formalizations/actions/runs?status='+status+'&per_page=100'
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'LightEFT-exact-gate'})) as response:data=json.load(response)
  others=[r for r in data['workflow_runs'] if str(r['id'])!=os.environ.get('GITHUB_RUN_ID')]
  ci.append(dict(status=status,other_ids=[r['id'] for r in others]));assert not others,ci
 save('ci-preflight.json',ci)
 assert not (ROOT/'.lake/build').exists() and not PKG.exists(),'clean checkout required'
 version=run('official-version',[str(TOOL/'bin/lean'),'--version'],[ROOT/'lean-toolchain'])
 assert 'version 4.34.0' in version and '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b' in version
 save('toolchain-hashes.json',{str(p):h(p.read_bytes()) for p in [TOOL/'bin/lean',TOOL/'bin/leanchecker',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']})
 PKG.mkdir(parents=True)
 for pin in pins:
  d=PKG/pin['name'];d.mkdir()
  capture('init-'+pin['name'],['git','init','-q',str(d)])
  capture('remote-'+pin['name'],['git','remote','add','origin',pin['url']],d)
  capture('fetch-'+pin['name'],['git','fetch','--depth','1','origin',pin['rev']],d)
  capture('checkout-'+pin['name'],['git','checkout','--detach','FETCH_HEAD'],d)
  assert git('rev-parse','HEAD',cwd=d)==pin['rev']
 save('dependency-pins.json',pins)
 # Bootstrap the unmodified official cache CLI using sequential Lean compilation.
 # This avoids Lake's parallel build scheduler; no runtime shim or helper source edit.
 bootstrap=ROOT/'.cache-bootstrap';bootstrap.mkdir()
 os.environ['LEAN_PATH']=os.pathsep.join(map(str,[bootstrap]+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
 os.environ['LEAN_SRC_PATH']=os.pathsep.join(map(str,[ROOT]+[PKG/p['name'] for p in pins]))
 seen=set();order=[]
 def locate(n):
  for pin in pins:
   base=PKG/pin['name'];p=base/Path(*n.split('.')).with_suffix('.lean')
   if p.exists():return p,base
  return None
 def visit(n):
  if n in seen:return
  seen.add(n);found=locate(n)
  if found is None:return
  p,base=found
  for dep in imports(p):visit(dep)
  order.append((n,p,base))
 visit('Cache.Main')
 for n,p,base in order:
  out=bootstrap/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  run('cache-bootstrap-'+n,[str(TOOL/'bin/lean'),'-j1','--root='+str(base),'-o',str(out),str(p)],[p])
 run('official-cache-get',[str(TOOL/'bin/lean'),'-j1','--run',str(PKG/'mathlib/Cache/Main.lean'),'get'],[p for _,p,_ in order])
 # Derive exactly the LightEFT aggregate closure, with necessary LightSpanners support.
 mods={}
 for lib in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']:
  if lib['name'] not in ['LightEFTSpanners','LightSpanners']:continue
  base=ROOT/lib['srcDir']
  for p in base.rglob('*.lean'):
   if 'verification' not in p.relative_to(base).parts:mods['.'.join(p.relative_to(base).with_suffix('').parts)]=(p,base)
 seen=set();project=[]
 def project_visit(n):
  if n in seen:return
  seen.add(n);p,base=mods[n]
  for dep in imports(p):
   if dep in mods:project_visit(dep)
   elif not (dep.startswith(('Mathlib','Batteries.','Lean','Std','Aesop','Qq','ProofWidgets','Plausible','ImportGraph'))):raise RuntimeError('Unmapped project import '+dep)
  project.append(n)
 project_visit('LightEFTSpanners')
 assert len(project)==486 and len([n for n in project if n.startswith('LightEFTSpanners.')])==429
 assert set(n for n in mods if n.startswith('LightEFTSpanners.'))<=set(project)
 save('source-graph.json',[dict(module=n,path=str(mods[n][0].relative_to(ROOT)),sha256=h(mods[n][0].read_bytes())) for n in project])
 outroot=ROOT/'.lake/build/lib/lean';assert not outroot.exists();outroot.mkdir(parents=True)
 os.environ['LEAN_PATH']=os.pathsep.join(map(str,[outroot]+[PKG/p['name']/'.lake/build/lib/lean' for p in pins]+[TOOL/'lib/lean']))
 objects=[]
 for n in project:
  p,base=mods[n];out=outroot/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  raw=run('compile-'+n,[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(base),'-o',str(out),str(p)],[p])
  assert not re.search(r'^.*:\d+:\d+: warning:',raw,re.M)
  objects.append(dict(module=n,path=str(out.relative_to(ROOT)),sha256=h(out.read_bytes()),bytes=out.stat().st_size))
 save('objects.json',objects)
 replay_modules=[n for n in project if n!='LightEFTSpanners']
 assert len(replay_modules)==485
 assert all(not any(other.startswith(n+'.') for other in project) for n in replay_modules)
 for n in replay_modules:
  raw=run('replay-'+n,[str(TOOL/'bin/leanchecker'),'-v',n],[mods[n][0]])
  assert raw.strip()=='replaying '+n
 audit=ROOT/'scripts/LightEFTFullAudit.lean'
 raw=run('complete-owner-audit',[str(TOOL/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',str(audit)],[audit]+[mods[n][0] for n in project])
 assert not git('status','--porcelain','--untracked-files=no')
 for pin in pins:assert git('rev-parse','HEAD',cwd=PKG/pin['name'])==pin['rev'] and not git('status','--porcelain','--untracked-files=no',cwd=PKG/pin['name'])
 save('result.json',dict(source=SOURCE,status='PASS',compilations=len(project),singleton_replays=len(replay_modules),paper_leaves=429,support_leaves=56,aggregate_compiled=True,aggregate_replayed=False,aggregate_replay_reason="import-only aggregate; official checker uses prefix selection",strict_warning_headers=0,audit=raw,proof_source_unchanged=True,dependency_pins_verified=True))
 print('EXACT_SOURCE_PASS',SOURCE,'compilations',len(project),'singleton_replays',len(replay_modules),raw,flush=True)
except BaseException:
 (E/'failure.txt').write_text(traceback.format_exc());raise
finally:finalize()
