#!/usr/bin/env python3
"""Fresh bounded dispatcher replay/fixture/all-new closure gates; no automatic retry."""
from pathlib import Path
import argparse,datetime,fcntl,hashlib,importlib.util,json,os,re,signal,subprocess,time,uuid
ROOT=Path(__file__).resolve().parents[1]
D=Path('/workspace/shared/flow-final-dispatch-reconstruction-20261014')
TC=Path('/workspace/shared/formalization-toolchain-recovered-20261014')
S=D/'scripts/strict_compile.py'
spec=importlib.util.spec_from_file_location('dispatch_strict',S);strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
BUILD=ROOT/'dispatcher-validation';LOCK=Path('/workspace/shared/formalization-compiler.lock')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,sort_keys=True,indent=2)+'\n')
def need(b,s):
 if not b:raise RuntimeError(s)
def runtime_paths(dependency_path):
 paths=set()
 for root in [Path(x) for x in dependency_path.split(':')]+[TC/'lean-4.34.0-linux/lib']:
  if root.exists():
   for q in root.rglob('*'):
    if q.is_file() and (q.name.endswith(('.olean','.olean.private','.olean.server','.ir','.so')) or '.so.' in q.name):paths.add(str(q.resolve()))
 paths.update(str(q) for q in [TC/'lean-4.34.0-linux/bin/lean',TC/'lean-4.34.0-linux/bin/leanchecker',TC/'env.sh',TC/'project-env.sh',TC/'metadata/lake-manifest.json',strict.PARENT/'check_pinned_baseline.py'])
 return paths
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('mode',choices=['replay','smoke','audit']);ap.add_argument('--module',choices=strict.ORDER);ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--lock-timeout',type=float,default=180);a=ap.parse_args();need(0<a.seconds<=600 and 0<a.lock_timeout<=600,'bad cap');need((a.mode=='replay')==(a.module is not None),'replay requires exactly one --module')
 ident=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'-'+uuid.uuid4().hex[:6];attempt=BUILD/'attempts'/ident;attempt.mkdir(parents=True);log=attempt/'log.txt';log.write_text('');receipt=attempt/'receipt.json'
 r={'mode':a.mode,'module':a.module,'started_at':utc(),'status':'preflight','cap_seconds':a.seconds,'returncode':None,'threads':1,'lock':str(LOCK),'runner_sha256':sha(__file__),'log':str(log),'inputs':{},'scope':'Only this fresh named local gate; no production publication or positive whole-program fixture claim'}
 started=time.monotonic();held=None
 try:
  held=LOCK.open('a');deadline=time.monotonic()+a.lock_timeout
  while True:
   try:fcntl.flock(held,fcntl.LOCK_EX|fcntl.LOCK_NB);break
   except BlockingIOError:
    need(time.monotonic()<deadline,'compiler lock wait cap exceeded; no Lean process started');time.sleep(.1)
  r['lock_acquired_at']=utc()
  inputs={}
  def bind(p,expected=None):
   p=Path(p);h=sha(p);need(expected is None or h==expected,'hash mismatch: '+str(p));inputs[str(p)]=h;return h
  bind(__file__);bind(S)
  baseline_path=strict.PARENT/'logs/recovered-baseline722.json';bind(baseline_path);baseline=json.loads(baseline_path.read_text())
  need(baseline['returncode']==0 and baseline['inputs_unchanged'] and baseline.get('runtime_files_unchanged') and len(baseline.get('runtime_files',{}))==45734,'missing fresh pinned baseline runtime')
  need(baseline['command'][0]==str(TC/'lean-4.34.0-linux/bin/lean'),'baseline compiler path mismatch')
  need(runtime_paths(baseline['dependency_lean_path'])==set(baseline['runtime_files']),'runtime inventory changed')
  for q,h in baseline['runtime_files'].items():bind(q,h)
  r['runtime_baseline_receipt']=str(baseline_path);r['runtime_files_count']=len(baseline['runtime_files'])
  plan=strict.baseline();strict.refresh_flat_overlay(plan);state=strict.state();env=strict.load_environment();env['LEAN_NUM_THREADS']='1';need(env['LEAN_SYSROOT']==baseline['lean_sysroot'] and env['FORMALIZATION_DEPENDENCY_LEAN_PATH']==baseline['dependency_lean_path'],'runtime search path changed')
  allbind={}
  for m in strict.MODULES:
   need(m in state['successes'],'missing successful strict module: '+m)
   allbind[m]=strict.validate_success(m,state['successes'][m],sha(strict.source(m)))
  for m in strict.MODULES:
   allbind.update(strict.capture_bindings(m,plan,state))
  parent=json.loads((strict.PARENT/'object-receipts.json').read_text())
  for m,h in plan['sources'].items():
   src=strict.source(m);obj=strict.PARENT/'lib'/strict.rel(m,'.olean');need(parent[m]['returncode']==0 and parent[m]['source_unchanged'],'bad parent receipt')
   bind(src,h);bind(obj,parent[m]['olean_sha256'])
  for m,b in allbind.items():
   bind(b['source'],b['source_sha256']);bind(b['object'],b['object_sha256'])
   for suffix in ['.server','.private']:need(not Path(b['object']+suffix).exists(),'unbound split object '+b['object']+suffix)
   if b['kind']=='new_strict':
    bind(b['successful_receipt'],b['successful_receipt_sha256']);bind(b['successful_log'],b['successful_log_sha256'])
    sr=json.loads(Path(b['successful_receipt']).read_text());bind(sr['source_snapshot'],b['source_sha256']);bind(sr['output_candidate'],b['object_sha256'])
  for q in [TC/'env.sh',TC/'project-env.sh',Path(env['LEAN']),TC/'lean-4.34.0-linux/bin/leanchecker',TC/'metadata/recovery-verification.json',TC/'metadata/lake-manifest.json']:bind(q)
  r['lean_path']=env['LEAN_PATH'];r['lean_sysroot']=env.get('LEAN_SYSROOT');r['strict_bindings']={m:allbind[m] for m in strict.MODULES}
  successes_path=BUILD/'successes.json';successes=json.loads(successes_path.read_text()) if successes_path.exists() else {}
  if a.mode!='replay':
   for m in strict.MODULES:
    key='replay:'+m;need(key in successes,'missing official replay '+m);q=Path(successes[key]['receipt']);bind(q,successes[key]['receipt_sha256']);previous=json.loads(q.read_text());need(previous['status']=='success' and previous['returncode']==0,'replay failed');need(set(previous['strict_bindings'])==set(strict.MODULES),'incomplete replay module bindings')
    for replay_module in strict.MODULES:
     need(all(previous['strict_bindings'][replay_module][k]==allbind[replay_module][k] for k in ['source_sha256','object_sha256']),'stale replay module binding '+replay_module)
    for old_path,old_hash in previous['inputs'].items():
     need(inputs.get(old_path,old_hash)==old_hash,'stale replay input '+old_path)
     if old_path not in inputs:bind(old_path,old_hash)
    bind(previous['log'],previous['log_sha256'])
  if a.mode=='replay':
   module='DirectedFlowCutGap.'+a.module;cmd=[str(TC/'lean-4.34.0-linux/bin/leanchecker'),'-v',module];key='replay:'+module;cwd=attempt
  else:
   filename={'smoke':'FinalDispatchSmoke.lean','audit':'FinalDispatchAllDeclarationsSafetyAudit.lean'}[a.mode];src=D/'verification'/filename;bind(src);snapshot=attempt/filename;snapshot.write_bytes(src.read_bytes());bind(snapshot,inputs[str(src)]);cmd=[env['LEAN'],'-j1','-DautoImplicit=false','-DwarningAsError=true']+(['--run'] if a.mode=='smoke' else [])+[str(snapshot)];key=a.mode;cwd=attempt;r['gate_source']=str(src)
  r.update(command=cmd,inputs=inputs,status='running');save(receipt,r)
  with log.open('w') as f:
   proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(held.fileno(),))
   try:rc=proc.wait(timeout=a.seconds)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=124
  r['returncode']=rc;r['inputs_unchanged']=runtime_paths(baseline['dependency_lean_path'])==set(baseline['runtime_files']) and all(Path(q).exists() and sha(q)==h for q,h in inputs.items());need(rc==0,'process exit '+str(rc));need(r['inputs_unchanged'],'input binding changed');txt=log.read_text();need('error:' not in txt,'error marker')
  if a.mode=='replay':need(re.findall(r'^replaying (.+)$',txt,re.M)==[module],'wrong official replay marker')
  elif a.mode=='smoke':
   names=re.findall(r'^PASS final dispatcher physical degenerate (\S+) instructions=(\d+) physicalOperationsIncludingHalt=(\d+) terminalOperations=(\d+)$',txt,re.M);need([x[0] for x in names]==['empty','one-zero-no-demands','self-demand','two-unit-direct'],'wrong physical case inventory');r['physical_degenerate_cases']=[dict(zip(['name','instructions','operations_including_halt','terminal_operations'],x)) for x in names]
  else:
   pairs=re.findall(r'^FINAL_DISPATCH_NEW_DECLARATION ([^|]+)\|(.+)$',txt,re.M);need(len(pairs)>0 and len(pairs)==len(set(n for _,n in pairs)),'bad new inventory');need(set(m for m,_ in pairs)==set(strict.MODULES),'missing new module');m=re.findall(r'^FINAL_DISPATCH_ALL_NEW_TYPE_BODY_CLOSURE_UNION passed: (\d+) roots; (\d+) constants; (\d+) edges; axioms (.+)$',txt,re.M);need(len(m)==1 and int(m[0][0])==len(pairs),'bad all-new closure marker');r['new_declarations']=len(pairs);r['closure_union']=m[0];inventory=attempt/'new-declarations.json';save(inventory,{n:m for m,n in pairs});r['inventory']=str(inventory);r['inventory_sha256']=sha(inventory)
  r['status']='success'
 except Exception as e:r['status']='capped' if r['returncode']==124 else 'failed';r['error']=str(e)
 finally:
  r['ended_at']=utc();r['elapsed_seconds']=time.monotonic()-started;r['log_sha256']=sha(log);save(receipt,r)
  if r['status']=='success':successes[key]={'receipt':str(receipt),'receipt_sha256':sha(receipt)};save(successes_path,successes)
  if held:fcntl.flock(held,fcntl.LOCK_UN);held.close()
 print(json.dumps({k:r[k] for k in ['mode','module','status','returncode','elapsed_seconds','log']}|{'receipt':str(receipt),'error':r.get('error')}),flush=True)
 return 0 if r['status']=='success' else 2
if __name__=='__main__':raise SystemExit(main())
