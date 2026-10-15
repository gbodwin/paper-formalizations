import os,pathlib,json,subprocess,time,hashlib
r=pathlib.Path.cwd();ev=r.parent/'evidence';env=os.environ.copy();env['ELAN_HOME']='/workspace/toolchains/elan';env['PATH']='/workspace/toolchains/elan/bin:'+env['PATH']
order=json.loads((ev/'order.json').read_text())
for it in order:
 m=it['module']
 if m=='SlackSparsification':continue
 # Lean Name prefix uses complete components. Require one exact object in the project output tree.
 objects=['.'.join(p.relative_to(r/'.lake/build/lib/lean').with_suffix('').parts) for p in (r/'.lake/build/lib/lean').rglob('*.olean')]
 assert [x for x in objects if x==m or x.startswith(m+'.')]==[m]
 cmd=['lake','env','leanchecker','-v',m];t=time.monotonic();p=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (ev/('checker-'+m+'.log')).write_text(p.stdout)
 row={'module':m,'command':cmd,'exit':p.returncode,'seconds':round(time.monotonic()-t,2),'olean_sha256':hashlib.sha256((r/'.lake/build/lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean')).read_bytes()).hexdigest()}
 with (ev/'checker-results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True);print(p.stdout,flush=True)
 if p.returncode or p.stdout.strip()!='replaying '+m:raise SystemExit(p.returncode or 2)
