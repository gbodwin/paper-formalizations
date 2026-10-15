import json,subprocess,pathlib,time,os,hashlib
root=pathlib.Path.cwd(); evidence=root.parent/'evidence'
env=os.environ.copy(); env['ELAN_HOME']='/workspace/toolchains/elan';env['PATH']='/workspace/toolchains/elan/bin:'+env['PATH']
order=json.loads((evidence/'order.json').read_text())
done={json.loads(s)['module'] for s in (evidence/'compile-results.jsonl').read_text().splitlines() if json.loads(s)['exit']==0}
for item in order:
 if item['module'] in done: continue
 mod=item['module']; out=root/'.lake/build/lib/lean'/pathlib.Path(*mod.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=['lake','env','lean','-j1','-DautoImplicit=false']+(['-DwarningAsError=true'] if item['strict'] else [])+['--root='+item['root'],'-o',str(out),item['source']]
 t=time.monotonic(); p=subprocess.run(cmd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (evidence/('compile-'+mod+'.log')).write_text(p.stdout)
 row={'module':mod,'command':cmd,'exit':p.returncode,'seconds':round(time.monotonic()-t,2),'source_sha256':hashlib.sha256(pathlib.Path(item['source']).read_bytes()).hexdigest()}
 with (evidence/'compile-results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if p.stdout: print(p.stdout,flush=True)
 if p.returncode: raise SystemExit(p.returncode)
 if p.stdout and (': warning:' not in p.stdout or any(': warning:' in line and not any(s in line for s in ['Variable name','This simp argument is unused',"try 'simp' instead",'automatically included section variable', 'Try this:', 'Used `tac1 <;> tac2`']) for line in p.stdout.splitlines())):
  print('STOP: diagnostic requires classification',flush=True);raise SystemExit(2)
