from pathlib import Path
import os,subprocess,time,json,hashlib
root=Path.cwd();ev=root/'checkpoints/subset-plus2-cgk13-20261015/evidence'
env=os.environ.copy();env['ELAN_HOME']='/workspace/toolchains/elan';env['PATH']='/workspace/toolchains/elan/bin:'+env['PATH']
mods=['Core','Paths','Charging','Incidence','Parameters','Clustering']
for name in mods+['Audit']:
 if name=='Audit':cmd=['lake','env','lean','-j1','-DautoImplicit=false','-DwarningAsError=true','A Note on Distance-Preserving Graph Sparsification/verification/SubsetPlusTwoAudit.lean']
 else:
  module='SlackSparsification.SubsetPlusTwo'+name
  names=['.'.join(p.relative_to(root/'.lake/build/lib/lean').with_suffix('').parts) for p in (root/'.lake/build/lib/lean').rglob('*.olean')]
  assert [n for n in names if n==module or n.startswith(module+'.')]==[module]
  cmd=['lake','env','leanchecker','-v',module]
 t=time.monotonic();r=subprocess.run(cmd,env=env,text=True,capture_output=True)
 (ev/('replay-'+name+'.log')).write_text(r.stdout+r.stderr)
 (ev/('replay-'+name+'.json')).write_text(json.dumps({'command':cmd,'exit':r.returncode,'seconds':time.monotonic()-t},indent=2))
 print(name,r.returncode,r.stdout+r.stderr,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 if name!='Audit':assert (r.stdout+r.stderr).strip()=='replaying '+module
