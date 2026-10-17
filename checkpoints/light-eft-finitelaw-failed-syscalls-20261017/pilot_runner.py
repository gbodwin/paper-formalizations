"""One bounded import attempt. No command-line execution entry point.
Production run_once is for subsequent reviewed authorization only; tests patch
validate_plan to permit harmless Python, never a replacement Lean executable.
"""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,resource,select,shutil,signal,subprocess,sys,time,uuid
HERE=Path(__file__).resolve().parent
REPO=HERE.parent.parent
sys.path.insert(0,str(REPO/'scripts'))
import LightEFTProcessLifecycle as life
from pilot_accounting import VisibleAccounting
from pilot_child import LIMITS
import integrated_housekeeping as housekeeping
LOCK=Path('/tmp/distance-sparsification-single-compiler.lock')
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux')
LEAN=TOOL/'bin/lean'
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
TRACER=Path('/usr/bin/strace')
TRACER_SHA='69f88291a4e47f258b8e32b089c919a247509f063ef3d6afe5389939051102b3'
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
PACKAGES=Path('/workspace/paper-formalizations/.lake/packages')
PILOT=REPO/'.lake/finitelaw-bounded-chain-20261017-4ba0428af86f49edab8807443909f413'
EVIDENCE=HERE/'evidence'
OUT=PILOT/'objects'
MODULE='LightEFTSpanners.FiniteLaw'
MODULE_ROOT=REPO/'Light Edge Fault Tolerant Graph Spanners'
PROJECT_SOURCE=MODULE_ROOT/'LightEFTSpanners/FiniteLaw.lean'
PROJECT_SHA='7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240'
RESOLVER=REPO/'scripts/LightEFTResolveCheckerTarget.lean'
RESOLVER_SHA='9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf'
CHECKER=TOOL/'bin/leanchecker'
CHECKER_SHA='ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'
OBJECT=OUT/'LightEFTSpanners/FiniteLaw.olean'
RESOLUTION=PILOT/'resolution.json'
MAP=REPO/'checkpoints/light-eft-provenance-fixes-20261017/evidence/dependency-map.json'
MAP_SHA='7c5150b666457ce16e835cdb2b5044ea8d2a29f005d05a79d5cbaf772af540b5'
INTERVAL=.25
DEADLINE=90.0
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir')

from pilot_cache_advice import hash_input, load_inventory

def digest(path,expected=None,advice_log=None):
    return hash_input(path,expected,advice_log)

def dep_roots():
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    if digest(MAP)['sha256']!=MAP_SHA:raise RuntimeError('Frozen dependency map changed')
    used={row['package'] for row in json.loads(MAP.read_text())['modules']}
    return [PACKAGES/p['name']/'.lake/build/lib/lean' for p in pins if p['name'] in used]+[TOOL/'lib/lean']

def environment(stage):
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_SYSROOT':str(TOOL),
        'LEAN_PATH':os.pathsep.join(map(str,[OUT]+dep_roots())),
        'LEAN_SRC_PATH':os.pathsep.join([str(MODULE_ROOT)]+[str(PACKAGES/p['name']) for p in pins]+[str(TOOL/'src/lean')])}
    env['MIMALLOC_ARENA_RESERVE']='128MiB'
    if stage=='compile':env['MIMALLOC_VERBOSE']='1'
    if stage=='resolve':env.update(LIGHTEFT_CHECKER_TARGET=MODULE,LIGHTEFT_CHECKER_RESOLUTION_FILE=str(RESOLUTION))
    if stage=='replay':env.update(LEAN_NUM_THREADS='1',LEAN_STACK_SIZE_KB='65536')
    return env

def production_inputs(source):
    files={source,MAP,LEAN,Path(sys.executable).resolve(),HERE/'pilot_runner.py',HERE/'pilot_child.py',HERE/'pilot_accounting.py',HERE/'pilot_cache_advice.py',HERE/'chain.py',HERE/'trace_supervisor.py',TRACER,HERE/'pid_observations.py',HERE/'integrated_housekeeping.py',HERE/'history-whitelist.json',PROJECT_SOURCE,RESOLVER,CHECKER,REPO/'scripts/LightEFTProcessLifecycle.py',REPO/'lake-manifest.json',REPO/'lean-toolchain'}
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    for p in pins:
        base=PACKAGES/p['name']
        # Read-only git inspection; this completes before the supervised child.
        if subprocess.check_output(['git','rev-parse','HEAD'],cwd=base,text=True).strip()!=p['rev']:raise RuntimeError('Package pin drift')
        if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=base):raise RuntimeError('Package source drift')
        files.update(base.rglob('*.lean'))
    for root in dep_roots():
        if not root.is_dir() or root.is_symlink():raise RuntimeError('Missing/symlink dependency root')
        for p in root.rglob('*'):
            if p.is_symlink():raise RuntimeError('Symlink in dependency search tree')
            if p.is_file() and (str(p).endswith(SUFFIXES) or '.so' in p.name):
                if p.relative_to(root).parts[0].split('.')[0] in ('LightEFTSpanners','LightSpanners'):raise RuntimeError('Inherited project object')
                files.add(p)
    return sorted(files)

def object_inventory():
    return [digest(p) for p in sorted(OUT.rglob('*')) if p.is_file()]

def stage_argv(stage):
    flags=['-j1','-s65536','-M512','-DautoImplicit=false','-DwarningAsError=true']
    if stage=='compile':return [str(LEAN),*flags,'--root='+str(MODULE_ROOT),'-o',str(OBJECT),str(PROJECT_SOURCE)]
    if stage=='resolve':return [str(LEAN),*flags,str(RESOLVER)]
    if stage=='replay':return [str(CHECKER),'-v',MODULE]
    raise ValueError('No other stage authorized')

def verify_resolution():
    data=json.loads(RESOLUTION.read_text())
    if data['target']!=MODULE or data['count']!=1 or data['resolved']!=[{'module':MODULE,'object':str(OBJECT)}]:raise RuntimeError('Official resolution not exact singleton/new object')
    found=[]
    for root in [OUT]+dep_roots():
        for path in root.rglob('*.olean'):
            name='.'.join(path.relative_to(root).with_suffix('').parts)
            if name==MODULE or name.startswith(MODULE+'.'):found.append((name,str(path)))
    if found!=[(MODULE,str(OBJECT))]:raise RuntimeError('Missing/shadowed/prefix-expanded checker object')
    return data

def validate_plan(plan):
    stage=plan['stage']
    if stage!='compile':raise RuntimeError('Diagnostic permits compilation only')
    source=RESOLVER if stage=='resolve' else PROJECT_SOURCE
    if plan['argv']!=stage_argv(stage) or plan['env']!=environment(stage) or plan['cwd']!=str(PILOT) or plan['source']!=str(source):raise RuntimeError('Not the exact finite authorized stage')
    for path,expected in [(TRACER,TRACER_SHA),(LEAN,LEAN_SHA),(CHECKER,CHECKER_SHA),(PROJECT_SOURCE,PROJECT_SHA),(RESOLVER,RESOLVER_SHA)]:
        if digest(path)['sha256']!=expected:raise RuntimeError('Pinned source/executable/harness drift: '+str(path))
    expected_inputs=production_inputs(source)
    if stage!='compile':
        if object_inventory()!=plan['object_bindings']:raise RuntimeError('Fresh output inventory changed')
        if not OBJECT.is_file():raise RuntimeError('No fresh target object')
        expected_inputs += [Path(r['path']) for r in plan['object_bindings']]
    if stage=='replay':
        verify_resolution();expected_inputs.append(RESOLUTION)
    expected_inputs=list(map(str,sorted(set(expected_inputs))))
    if plan['inputs'] is None:plan['inputs']=expected_inputs
    elif plan['inputs']!=expected_inputs:raise RuntimeError('Incomplete input inventory')

def child_status(pid):
    fields=Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()
    raw=Path(f'/proc/{pid}/status').read_text()
    values={k:int(v.split()[0])*1024 for line in raw.splitlines() if ':' in line for k,v in [line.split(':',1)] if k in ('VmRSS','VmSize')}
    return dict(pid=pid,ppid=int(fields[1]),pgid=int(fields[2]),sid=int(fields[3]),start_ticks=int(fields[19]),state=fields[0],rss=values.get('VmRSS',0),vm=values.get('VmSize',0))

def check_memory(now,baseline,minimum):
    if now['headroom']<minimum:raise RuntimeError('Visible headroom below required floor')
    for a,b in zip(now['nodes'],baseline['nodes'],strict=True):
        if a['path']!=b['path'] or a['limit']!=b['limit']:raise RuntimeError('Accounting limit changed')
        if any(a['oom'][k]!=b['oom'][k] for k in b['oom']):raise RuntimeError('OOM counters changed')
        if a['pids_max']!=b['pids_max'] or a['pids_events']!=b['pids_events']:raise RuntimeError('PID limit/events changed')
        if a['pids_max']!='max' and a['pids_current']>=int(a['pids_max']):raise RuntimeError('Visible PID limit exhausted')

def verify_ready(packet,child,lockfd,first):
    if 'error' in packet:raise RuntimeError('Child limit setup/readback failure: '+packet['error'])
    st=os.fstat(lockfd)
    expected={k:[v,v] for k,v in LIMITS.items()}
    if packet['limits']!=expected:raise RuntimeError('Child limit readback mismatch')
    for name,value in LIMITS.items():
        if resource.prlimit(child.pid,getattr(resource,name))!=(value,value):raise RuntimeError('Kernel limit readback mismatch')
    current=child_status(child.pid)
    if current['start_ticks']!=first['start_ticks'] or current['ppid']!=os.getpid():raise RuntimeError('Child identity changed')
    for key in ('sid','pgid'):
        if packet[key]!=child.pid or current[key]!=child.pid:raise RuntimeError('No isolated session')
    remote=os.stat(f'/proc/{child.pid}/fd/{lockfd}')
    if packet['pid']!=child.pid or packet['ppid']!=os.getpid() or packet['lock_fd']!=lockfd or not packet['lock_inheritable']:raise RuntimeError('Bad lock handshake')
    if [packet['lock_device'],packet['lock_inode']]!=[st.st_dev,st.st_ino] or (remote.st_dev,remote.st_ino)!=(st.st_dev,st.st_ino):raise RuntimeError('Inherited lock identity mismatch')

def owned_wait4(child,record):
    if child.returncode is not None:return True
    pid,status,usage=os.wait4(child.pid,os.WNOHANG)
    if not pid:return False
    child.returncode=os.waitstatus_to_exitcode(status)
    record.update(exit=child.returncode,direct_wait_owner='runner wait4',direct_reaped=True,wait4_maxrss_kib=usage.ru_maxrss)
    return True

def reap_direct(child,record,save):
    began=time.monotonic()
    while not owned_wait4(child,record):
        sig=signal.SIGTERM if time.monotonic()-began<1 else signal.SIGKILL
        try:os.kill(child.pid,sig)
        except ProcessLookupError:pass
        time.sleep(.02)

if __name__=='__main__':raise SystemExit('Use compile-only diagnostic entry point.')
