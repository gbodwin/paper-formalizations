import os,subprocess,time,json,pathlib
r=pathlib.Path.cwd();ev=r.parent/'evidence';env=os.environ.copy();env['ELAN_HOME']='/workspace/toolchains/elan';env['PATH']='/workspace/toolchains/elan/bin:'+env['PATH']
cmd=['lake','env','lean','-j1','-DautoImplicit=false','-DwarningAsError=true','A Note on Distance-Preserving Graph Sparsification/verification/PlusSixAudit.lean']
t=time.monotonic();p=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(ev/'recursive-audit.log').write_text(p.stdout)
row={'command':cmd,'exit':p.returncode,'seconds':round(time.monotonic()-t,2)}
(ev/'audit-result.json').write_text(json.dumps(row,indent=2));print(json.dumps(row));print(p.stdout);raise SystemExit(p.returncode)
