#!/usr/bin/env python3
"""Fresh732 full ownership + all-new type/body union audit. Prepared, not automatic."""
from pathlib import Path
import argparse,datetime,fcntl,importlib.util,json,os,re,signal,subprocess,time,uuid
ROOT=Path(__file__).resolve().parents[1]
RUNNER=Path('/workspace/shared/flow-final-envelope-reconstruction-20261014/scripts/run_gates.py')
spec=importlib.util.spec_from_file_location('envelope_gates',RUNNER);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
SOURCE=ROOT/'FinalIntegrationFullRootAudit.lean';BUILD=ROOT/'full-union-validation'
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seconds',type=float,default=300);p.add_argument('--lock-timeout',type=float,default=360);a=p.parse_args();g.need(0<a.seconds<=600 and 0<a.lock_timeout<=600,'invalid cap')
 ident=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'-'+uuid.uuid4().hex[:6];attempt=BUILD/'attempts'/ident;attempt.mkdir(parents=True);log=attempt/'audit.log';log.write_text('');receipt=attempt/'receipt.json';inputs=g.Snapshot();r={'status':'preflight','started_at':g.utc(),'returncode':None,'cap_seconds':a.seconds,'lock_timeout':a.lock_timeout,'log':str(log),'threads':1,'source':str(SOURCE),'scope':'Fresh full732 name preservation and all-ten-new-module type/body dependency union only; no physical execution or publication claim'};held=None;started=time.monotonic()
 try:
  held=g.LOCK.open('a');deadline=time.monotonic()+a.lock_timeout
  while True:
   try:fcntl.flock(held,fcntl.LOCK_EX|fcntl.LOCK_NB);break
   except BlockingIOError:g.need(time.monotonic()<deadline,'bounded compiler-lock wait exhausted');time.sleep(.1)
  r['lock_acquired_at']=g.utc();inputs.add(Path(__file__));inputs.add(RUNNER);inputs.add(SOURCE);env=g.load_environment(inputs);runtime_before=g.pin_runtime(inputs,env);plan,base=g.baseline_bindings(inputs);bindings=g.dispatcher_bindings(inputs,base);g.overlay(bindings)
  strict=g.require_gate(inputs,'strict');replay=g.require_gate(inputs,'replay',strict['envelope_object_sha256']);r['envelope_strict']=strict;r['envelope_replay']=replay
  old=g.fresh_baseline(inputs,base);snapshot=attempt/'FinalIntegrationFullRootAudit.lean';snapshot.write_bytes(SOURCE.read_bytes());inputs.add(snapshot,inputs.files[str(SOURCE)])
  cmd=[env['LEAN'],'-j1','-DautoImplicit=false','-DwarningAsError=true',str(snapshot)];r.update(command=cmd,lean_path=env['LEAN_PATH'],inputs=dict(inputs.files),status='running');g.write_json(receipt,r)
  with log.open('w') as out:
   proc=subprocess.Popen(cmd,cwd=attempt,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(held.fileno(),))
   try:r['returncode']=proc.wait(timeout=a.seconds)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();r['returncode']=124
  r['changed_inputs']=inputs.verify();r['runtime_inventory_unchanged']=g.runtime_paths(env)==runtime_before;r['inputs_unchanged']=not r['changed_inputs'] and r['runtime_inventory_unchanged'];g.need(r['returncode']==0,'Lean exit '+str(r['returncode']));g.need(r['inputs_unchanged'],'inputs changed');txt=log.read_text();g.need('error:' not in txt,'error marker');owners=g.parse_attribution(txt);g.need(set(owners.values())==set(base)|g.NEW_MODULES,'module attribution differs from exact732')
  missing=sorted(set(old)-set(owners));additions=sorted(set(owners)-set(old));shifts=[{'name':n,'old_owner':old[n],'new_owner':owners[n]} for n in sorted(set(old)&set(owners)) if old[n]!=owners[n]];g.need(not missing,'lost old names');g.need(all(owners[n] in g.NEW_MODULES for n in additions),'addition owned outside new modules')
  passes=re.findall(r'^FINAL_INTEGRATION_MODULE_AUDIT passed: ([^;]+); (\d+) declarations$',txt,re.M);g.need(len(passes)==10 and set(m for m,_ in passes)==g.NEW_MODULES,'new module passes incomplete');owned=sum(int(n) for _,n in passes);counts=re.findall(r'^PASS exhaustive reference closure axiom audit: (\d+) declarations$',txt,re.M);g.need(counts==[str(len(owners))],'full count mismatch');g.need('FINAL_INTEGRATION_MODULE_COUNT passed: 732 defining modules' in txt,'module count missing');union=re.findall(r'^FINAL_INTEGRATION_ALL_NEW_TYPE_BODY_CLOSURE passed: (\d+) roots; (\d+) constants; axioms (.+)$',txt,re.M);g.need(len(union)==1 and int(union[0][0])==owned,'union misses some selected new roots')
  names=attempt/'full-name-inventory.json';g.write_json(names,owners);r.update(status='success',full_declarations=len(owners),new_owned_declarations=owned,distinct_additions=len(additions),ownership_shifts=shifts,old_names_preserved=len(old),union=union[0],names=str(names),names_sha256=g.sha(names));g.write_json(attempt/'name-comparison.json',{'missing':missing,'additions':additions,'ownership_shifts':shifts})
 except Exception as e:r['status']='capped' if r['returncode']==124 else 'failed';r['error']=str(e)
 finally:
  r['ended_at']=g.utc();r['elapsed_seconds']=time.monotonic()-started;r['log_sha256']=g.sha(log);g.write_json(receipt,r)
  if r['status']=='success':g.write_json(BUILD/'success.json',{'receipt':str(receipt),'receipt_sha256':g.sha(receipt)})
  if held:fcntl.flock(held,fcntl.LOCK_UN);held.close()
 print(json.dumps({k:r.get(k) for k in ['status','returncode','elapsed_seconds','full_declarations','new_owned_declarations','distinct_additions','error']}|{'receipt':str(receipt)}),flush=True);return 0 if r['status']=='success' else 2
if __name__=='__main__':raise SystemExit(main())
