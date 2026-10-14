#!/usr/bin/env python3
"""Bounded, serialized strict compilation of NEW FinalDispatch production modules.

This script is itself unrun preparation. No compilation occurs without --module
or --batch-ready. --status is read-only. Each compiler child inherits the exact
exclusive flock held by its per-module wrapper; no lockless Lean probe is used.
"""
from __future__ import annotations
import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = Path('/workspace/shared/formalization-toolchain-recovered-20261014')
BASE = Path('/workspace/shared/flow-published722-recovered-20261014T0012Z')
PAPER = BASE/'Improved Upper Bounds for the Directed Flow-Cut Gap'
PARENT = Path('/workspace/shared/flow-rebuild722-20261014')
LOCK = Path('/workspace/shared/formalization-compiler.lock')
BUILD = ROOT/'strict-build'
LIB = BUILD/'lib'
BASE_COMMIT = 'ea1dfba989c89eb8ceed693cdad42ba8d96584f5'
ORDER = ['FinalDispatchProgram','FinalDispatchCallLift','FinalDispatchCalls',
         'FinalDispatchPrefix','FinalDispatchOutput','FinalDispatchPositive',
         'FinalDispatchTail','FinalDispatchTrace','ActualFinalDispatch']
MODULES = ['DirectedFlowCutGap.'+short for short in ORDER]
NEW = set(MODULES)

class Blocked(RuntimeError):
    pass

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()

def rel(module: str, suffix: str) -> Path:
    return Path(*module.split('.')).with_suffix(suffix)

def source(module: str) -> Path:
    return (ROOT if module in NEW else PAPER)/rel(module,'.lean')

def read_json(path: Path, default=None):
    if not path.exists() and default is not None:
        return default
    return json.loads(path.read_text())

def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp = path.with_name(path.name+'.tmp-'+uuid.uuid4().hex)
    tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
    os.replace(tmp,path)

def state():
    return read_json(BUILD/'state.json',{'successes':{},'latest_attempts':{}})

def imports(path: Path) -> list[str]:
    # All permitted production files use simple, one-line imports.
    return [w for line in re.findall(r'^import\s+([^\n]+)',path.read_text(),re.M)
            for w in line.split() if w.startswith('DirectedFlowCutGap.')]

def closure(module: str, baseline_sources: dict[str,str]) -> list[str]:
    done,visiting,out = set(),set(),[]
    def visit(name):
        if name in done:
            return
        if name in visiting:
            raise Blocked('Import cycle at '+name)
        if name not in NEW and name not in baseline_sources:
            raise Blocked('Import outside new modules and exact722: '+name)
        visiting.add(name)
        for dep in imports(source(name)):
            visit(dep)
        visiting.remove(name)
        done.add(name)
        out.append(name)
    visit(module)
    return out[:-1]

def load_environment() -> dict[str,str]:
    # Reads the prescribed scripts; this shell never launches Lean.
    command = 'set -eu; source "$1/env.sh"; source "$1/project-env.sh"; env -0'
    raw = subprocess.check_output(['bash','--noprofile','--norc','-c',command,'bash',str(TOOLCHAIN)])
    env = dict(x.split('=',1) for x in raw.decode().split('\0') if x)
    dep = env['FORMALIZATION_DEPENDENCY_LEAN_PATH'].split(':')
    if any((Path(p)/'DirectedFlowCutGap').exists() for p in dep):
        raise Blocked('A dependency LEAN_PATH root shadows DirectedFlowCutGap')
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_PATH'] = ':'.join([str(LIB),*dep])
    env['LEAN_SRC_PATH'] = str(ROOT)+':'+env['FORMALIZATION_DEPENDENCY_SRC_PATH']
    return env

def baseline():
    plan = read_json(PARENT/'rebuild-plan.json')
    if plan['commit'] != BASE_COMMIT or len(plan['sources']) != 722:
        raise Blocked('Parent rebuild plan is not the exact722 baseline')
    commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE,text=True).strip()
    if commit != BASE_COMMIT:
        raise Blocked('Published checkout commit changed')
    return plan

def validate_success(module: str, record: dict, source_hash: str) -> dict:
    receipt_path = Path(record['receipt'])
    if sha(receipt_path) != record['receipt_sha256']:
        raise Blocked('Strict receipt changed: '+module)
    receipt = read_json(receipt_path)
    obj = LIB/rel(module,'.olean')
    log = Path(receipt['log'])
    snapshot = Path(receipt['source_snapshot'])
    if receipt.get('status') != 'success' or receipt.get('returncode') != 0:
        raise Blocked('No successful strict receipt: '+module)
    if receipt.get('threads') != 1 or not {'-j1','-DautoImplicit=false','-DwarningAsError=true'}.issubset(receipt.get('command',[])):
        raise Blocked('Receipt does not attest the required strict compiler flags: '+module)
    if receipt['source_sha256'] != source_hash or sha(snapshot) != source_hash:
        raise Blocked('Successful strict source binding is stale: '+module)
    if obj.is_symlink() or not obj.is_file() or sha(obj) != receipt['output_object_sha256']:
        raise Blocked('Successful strict object binding is stale: '+module)
    if sha(log) != receipt['log_sha256']:
        raise Blocked('Successful strict log binding is stale: '+module)
    for name,binding in receipt['imports'].items():
        path = source(name)
        if sha(path) != binding['source_sha256']:
            raise Blocked('Imported source changed since strict receipt: '+module+' -> '+name)
        path = LIB/rel(name,'.olean') if name in NEW else PARENT/'lib'/rel(name,'.olean')
        if sha(path) != binding['object_sha256']:
            raise Blocked('Imported object changed since strict receipt: '+module+' -> '+name)
    return {'kind':'new_strict','source':str(source(module)),'source_sha256':source_hash,
            'object':str(obj),'object_sha256':receipt['output_object_sha256'],
            'successful_receipt':str(receipt_path),'successful_receipt_sha256':sha(receipt_path),
            'successful_log':str(log),'successful_log_sha256':sha(log)}

def capture_bindings(module: str, plan: dict, strict_state: dict) -> dict:
    parents = read_json(PARENT/'object-receipts.json',{})
    result = {}
    for name in closure(module,plan['sources']):
        src = source(name)
        src_hash = sha(src)
        if name in NEW:
            record = strict_state['successes'].get(name)
            if not record:
                raise Blocked('New import has no successful strict receipt: '+name)
            result[name] = validate_success(name,record,src_hash)
        else:
            obj = PARENT/'lib'/rel(name,'.olean')
            r = parents.get(name)
            if not r or r.get('returncode') != 0 or not r.get('source_unchanged') or not obj.is_file():
                raise Blocked('Exact722 import is not rebuilt yet: '+name)
            if src_hash != plan['sources'][name] or src_hash != r['source_sha256']:
                raise Blocked('Exact722 source hash mismatch: '+name)
            if sha(obj) != r['olean_sha256']:
                raise Blocked('Exact722 object hash mismatch: '+name)
            result[name] = {'kind':'published722_rebuilt','source':str(src),'source_sha256':src_hash,
                            'object':str(obj),'object_sha256':r['olean_sha256'],
                            'parent_rebuild_receipt':r}
    return result

def refresh_flat_overlay(plan: dict) -> None:
    """Exactly one namespace root: all parent object files, then real new objects."""
    namespace = LIB/'DirectedFlowCutGap'
    namespace.mkdir(parents=True,exist_ok=True)
    expected = set()
    for obj in (PARENT/'lib'/'DirectedFlowCutGap').rglob('*'):
        if not obj.is_file():
            continue
        dest = namespace/obj.relative_to(PARENT/'lib'/'DirectedFlowCutGap')
        # No parent object or diagnostic object may acquire a new production name.
        stem = dest.name.split('.',1)[0]
        if 'DirectedFlowCutGap.'+stem in NEW:
            raise Blocked('Parent object collides with new production module: '+str(obj))
        if 'DirectedFlowCutGap.'+stem not in plan['sources']:
            raise Blocked('Unknown/diagnostic parent object: '+str(obj))
        expected.add(dest)
        dest.parent.mkdir(parents=True,exist_ok=True)
        if dest.is_symlink():
            if dest.resolve() != obj.resolve():
                raise Blocked('Wrong parent overlay target: '+str(dest))
        elif dest.exists():
            raise Blocked('Parent overlay slot contains a real object: '+str(dest))
        else:
            dest.symlink_to(obj)
    for obj in namespace.rglob('*'):
        if not obj.is_file() and not obj.is_symlink():
            continue
        stem = obj.name.split('.',1)[0]
        if obj not in expected and ('DirectedFlowCutGap.'+stem not in NEW or obj.is_symlink()):
            raise Blocked('Unexpected/diagnostic object in production overlay: '+str(obj))

def unchanged(bindings: dict) -> bool:
    for b in bindings.values():
        if sha(Path(b['source'])) != b['source_sha256'] or sha(Path(b['object'])) != b['object_sha256']:
            return False
        if b['kind']=='new_strict':
            if sha(Path(b['successful_receipt'])) != b['successful_receipt_sha256']:
                return False
            if sha(Path(b['successful_log'])) != b['successful_log_sha256']:
                return False
    return True

def compile_one(module: str, args, batch_deadline: float, batch_id: str) -> dict:
    ident = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'-'+uuid.uuid4().hex[:8]
    attempt_dir = BUILD/'attempts'/ident/module.rsplit('.',1)[1]
    attempt_dir.mkdir(parents=True,exist_ok=False)
    original = source(module)
    snapshot = attempt_dir/'source'/rel(module,'.lean')
    snapshot.parent.mkdir(parents=True,exist_ok=True)
    snapshot.write_bytes(original.read_bytes())
    log = attempt_dir/'strict.log'
    log.write_text('')
    receipt_path = attempt_dir/'receipt.json'
    output = attempt_dir/'output'/rel(module,'.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    r = {'module':module,'batch_id':batch_id,'started_at':utc(),'status':'preflight',
         'production_module':True,'source':str(original),'source_snapshot':str(snapshot),
         'source_sha256':sha(snapshot),'log':str(log),'output_candidate':str(output),
         'lock':str(LOCK),'threads':1,'auto_retry':False,'imports':{},'returncode':None}
    started = time.monotonic()
    lock = None
    acquired = False
    try:
        lock = LOCK.open('a')
        lock_deadline = min(batch_deadline,time.monotonic()+args.lock_timeout)
        while True:
            try:
                fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
                acquired = True
                break
            except BlockingIOError:
                if time.monotonic() >= lock_deadline:
                    raise Blocked('Exclusive compiler lock is busy; no Lean process launched')
                time.sleep(min(.1,max(0,lock_deadline-time.monotonic())))
        r['lock_acquired_at'] = utc()
        plan = baseline()
        refresh_flat_overlay(plan)
        env = load_environment()
        current = state()
        bindings = capture_bindings(module,plan,current)
        r['imports'] = bindings
        r['direct_imports'] = imports(snapshot)
        r['parent_rebuild_plan_sha256'] = sha(PARENT/'rebuild-plan.json')
        r['environment_scripts'] = {str(TOOLCHAIN/x):sha(TOOLCHAIN/x) for x in ['env.sh','project-env.sh']}
        r['lean_executable'] = env['LEAN']
        r['lean_executable_sha256'] = sha(Path(env['LEAN']))
        r['lean_path'] = env['LEAN_PATH']
        if sha(original) != r['source_sha256']:
            raise Blocked('Source changed during preflight')
        cap = min(args.module_timeout,batch_deadline-time.monotonic())
        if cap <= 0:
            raise Blocked('Overall batch deadline reached before launch')
        cmd = [env['LEAN'],'-j1','-DautoImplicit=false','-DwarningAsError=true',
               '-o',str(output),str(rel(module,'.lean'))]
        r.update(command=cmd,cap_seconds=cap,status='running')
        write_json(receipt_path,r)
        with log.open('wb') as out:
            proc = subprocess.Popen(cmd,cwd=attempt_dir/'source',env=env,stdout=out,stderr=subprocess.STDOUT,
                                    start_new_session=True,pass_fds=(lock.fileno(),))
            try:
                rc = proc.wait(timeout=cap)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL)
                proc.wait()
                rc = 124
        r['returncode'] = rc
        r['source_unchanged'] = sha(original)==r['source_sha256'] and sha(snapshot)==r['source_sha256']
        r['imports_unchanged'] = unchanged(bindings)
        r['environment_unchanged'] = all(sha(Path(p))==h for p,h in r['environment_scripts'].items())
        r['lean_executable_unchanged'] = sha(Path(env['LEAN']))==r['lean_executable_sha256']
        if rc == 124:
            r['status'] = 'capped'
        elif rc != 0:
            r['status'] = 'failed'
        elif not all(r[k] for k in ['source_unchanged','imports_unchanged','environment_unchanged','lean_executable_unchanged']):
            r['status'] = 'binding_changed'
        elif not output.is_file():
            r['status'] = 'missing_output'
        else:
            dest = LIB/rel(module,'.olean')
            if dest.is_symlink():
                raise Blocked('New production slot unexpectedly is a symlink')
            temp = dest.with_name(dest.name+'.tmp-'+ident)
            shutil.copyfile(output,temp)
            os.replace(temp,dest)
            # Hash the candidate/published object only after successful strict
            # exit and all source/import/toolchain postflight checks.
            r['output_object'] = str(dest)
            r['output_object_sha256'] = sha(dest)
            if sha(output) != r['output_object_sha256']:
                raise Blocked('Published strict object differs from retained candidate')
            r['status'] = 'success'
    except Exception as error:
        r['status'] = 'blocked' if r['returncode'] is None else 'postflight_failed'
        r['error'] = str(error)
        # No failed/capped object hash can be mistaken for a successful receipt.
        r.pop('output_object_sha256',None)
    finally:
        r['ended_at'] = utc()
        r['elapsed_seconds'] = time.monotonic()-started
        r['log_sha256'] = sha(log)
        write_json(receipt_path,r)
        if acquired:
            current = state()
            current['latest_attempts'][module] = {'receipt':str(receipt_path),'receipt_sha256':sha(receipt_path)}
            if r['status']=='success':
                current['successes'][module] = current['latest_attempts'][module]
            write_json(BUILD/'state.json',current)
            fcntl.flock(lock,fcntl.LOCK_UN)
        if lock:
            lock.close()
    print(json.dumps({'module':module,'status':r['status'],'receipt':str(receipt_path),
                      'returncode':r['returncode'],'elapsed_seconds':r['elapsed_seconds']}),flush=True)
    return {'module':module,'status':r['status'],'receipt':str(receipt_path),'receipt_sha256':sha(receipt_path)}

def current_success(module: str, s: dict) -> bool:
    record = s['successes'].get(module)
    if not record:
        return False
    try:
        validate_success(module,record,sha(source(module)))
        return True
    except (Blocked,OSError,KeyError,ValueError):
        return False

def choose_ready(plan: dict) -> tuple[str|None,str]:
    s = state()
    for module in MODULES:
        if current_success(module,s):
            continue
        last = s['latest_attempts'].get(module)
        if last:
            old = read_json(Path(last['receipt']))
            if old.get('status')!='success' and old.get('source_sha256')==sha(source(module)):
                return None,'Previous unchanged-source attempt needs explicit --module: '+module
        try:
            capture_bindings(module,plan,s)
            return module,'ready'
        except (Blocked,OSError,KeyError,ValueError) as error:
            return None,str(error)
    return None,'All nine production modules have current successful strict receipts'

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--module',choices=ORDER,help='Explicitly attempt exactly one production module once')
    action.add_argument('--batch-ready',type=int,metavar='N',help='Attempt at most N ready modules, stop on first failure/blocker')
    action.add_argument('--status',action='store_true',help='Read-only status; do not create an overlay or launch Lean')
    parser.add_argument('--module-timeout',type=float,default=120)
    parser.add_argument('--batch-timeout',type=float,default=600)
    parser.add_argument('--lock-timeout',type=float,default=5)
    args = parser.parse_args()
    if not (0<args.module_timeout<=600 and 0<args.batch_timeout<=1800 and 0<args.lock_timeout<=60):
        parser.error('Caps must be positive; module≤600s, batch≤1800s, lock≤60s')
    if args.batch_ready is not None and not 1<=args.batch_ready<=9:
        parser.error('--batch-ready must be between 1 and 9')
    plan = baseline()
    if args.status:
        s = state()
        statuses = {m:current_success(m,s) for m in MODULES}
        ready,reason = choose_ready(plan)
        print(json.dumps({'current_successful_strict_objects':statuses,'next_ready':ready,'reason':reason,
                          'lean_invoked':False},indent=2))
        return 0
    batch_id = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'-'+uuid.uuid4().hex[:8]
    started = time.monotonic()
    deadline = started+args.batch_timeout
    results = []
    reason = ''
    limit = 1 if args.module else args.batch_ready
    for _ in range(limit):
        if time.monotonic()>=deadline:
            reason='Overall batch deadline reached; no further module launched'
            break
        if args.module:
            module='DirectedFlowCutGap.'+args.module
        else:
            module,reason=choose_ready(plan)
            if module is None:
                break
        result=compile_one(module,args,deadline,batch_id)
        results.append(result)
        if result['status']!='success':
            reason='Stopped on first non-successful attempt; no auto-retry'
            break
    report={'batch_id':batch_id,'ended_at':utc(),'elapsed_seconds':time.monotonic()-started,
            'batch_cap_seconds':args.batch_timeout,'module_cap_seconds':args.module_timeout,
            'requested_module_limit':limit,'modules':results,'reason':reason,
            'lock_scope':'Exclusive per-module process lock, inherited by Lean; released between modules and batches',
            'scope':'Fresh strict source compilation only; no kernel replay, axiom-audit, physical-fixture or release-gate claim'}
    write_json(BUILD/'batches'/(batch_id+'.json'),report)
    print(json.dumps(report,indent=2),flush=True)
    return 0 if results and all(r['status']=='success' for r in results) else 2

if __name__=='__main__':
    sys.exit(main())
