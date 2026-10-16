from pathlib import Path
import os,subprocess,json,time,hashlib,sys,fcntl
compiler_lock=open("/tmp/distance-sparsification-single-compiler.lock","w")
fcntl.flock(compiler_lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
root=Path.cwd();ev=root/'checkpoints/directed-preservers-20261016/evidence';ev.mkdir(exist_ok=True)
env=os.environ.copy();env['ELAN_HOME']='/workspace/toolchains/elan';env['PATH']='/workspace/toolchains/elan/bin:'+env['PATH']
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],env=env,text=True).strip();env['LEAN_PATH']=base+':/workspace/plus-six-verification/checkpoint/candidate/.lake/build/lib/lean'
module=sys.argv[1];attempt=len(list(ev.glob('attempt-*.json')))+1
src=root/'A Note on Distance-Preserving Graph Sparsification'/('SlackSparsification/'+module+'.lean');out=root/'.lake/build/lib/lean/SlackSparsification'/(module+'.olean')
if module=='ConsistentTiebreaking':
 src=root/'New Results on Linear Size Distance Preservers/LinearDistancePreservers/ConsistentTiebreaking.lean';out=root/'.lake/build/lib/lean/LinearDistancePreservers/ConsistentTiebreaking.olean'
if module=='Aggregate':
 src=root/'A Note on Distance-Preserving Graph Sparsification/SlackSparsification.lean';out=root/'.lake/build/lib/lean/SlackSparsification.olean'
cmd=['/workspace/toolchains/lean-4.34.0-linux/bin/lean','-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(src.parent.parent if module!='Aggregate' else src.parent),'-o',str(out),str(src)]
if module=='ConsistentTiebreaking' and '--inherited' in sys.argv:cmd.remove('-DwarningAsError=true')
t=time.monotonic();p=subprocess.run(cmd,env=env,text=True,capture_output=True)
(ev/f'attempt-{attempt:03}.log').write_text(p.stdout+p.stderr)
(ev/f'attempt-{attempt:03}.json').write_text(json.dumps({'command':cmd,'LEAN_PATH':env['LEAN_PATH'],'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'exit':p.returncode,'seconds':time.monotonic()-t},indent=2))
(ev/f'attempt-{attempt:03}.lean').write_bytes(src.read_bytes());print(p.stdout+p.stderr);print('attempt',attempt,'exit',p.returncode);sys.exit(p.returncode)
