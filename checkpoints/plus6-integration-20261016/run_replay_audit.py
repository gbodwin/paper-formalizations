from pathlib import Path
import os,subprocess,time,json
root=Path.cwd();ev=root/'checkpoints/plus6-integration-20261016/evidence'
env=os.environ.copy();env['ELAN_HOME']='/workspace/toolchains/elan';env['PATH']=env['ELAN_HOME']+'/bin:'+env['PATH']
module='SlackSparsification.PlusSixIntegration'
names=['.'.join(p.relative_to(root/'.lake/build/lib/lean').with_suffix('').parts) for p in (root/'.lake/build/lib/lean').rglob('*.olean')]
assert [n for n in names if n==module or n.startswith(module+'.')]==[module]
commands=[('Integration',['lake','env','leanchecker','-v',module]),('Audit',['lake','env','lean','-j1','-DautoImplicit=false','-DwarningAsError=true','A Note on Distance-Preserving Graph Sparsification/verification/PlusSixIntegrationAudit.lean'])]
for name,cmd in commands:
 t=time.monotonic();r=subprocess.run(cmd,env=env,text=True,capture_output=True)
 (ev/f'replay-{name}.log').write_text(r.stdout+r.stderr)
 (ev/f'replay-{name}.json').write_text(json.dumps(dict(command=cmd,exit=r.returncode,seconds=time.monotonic()-t),indent=2)+'\n')
 print(name,r.returncode,r.stdout+r.stderr,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 if name=='Integration':assert (r.stdout+r.stderr).strip()=='replaying '+module
