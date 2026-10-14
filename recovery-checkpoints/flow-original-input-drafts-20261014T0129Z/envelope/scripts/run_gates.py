#!/usr/bin/env python3
"""Prepared, unlaunched FinalDispatchEnvelope validation runner.

Four explicit modes, each with one bounded child and the shared exclusive
compiler lock. No automatic execution, batching, or retries. A successful
receipt attests only its named gate, never publication or physical fixtures.
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
REBUILD = Path('/workspace/shared/flow-rebuild722-20261014')
DISPATCH = Path('/workspace/shared/flow-final-dispatch-reconstruction-20261014')
LOCK = Path('/workspace/shared/formalization-compiler.lock')
BUILD = ROOT/'gate-build'
LIB = BUILD/'lib'
BASE_COMMIT = 'ea1dfba989c89eb8ceed693cdad42ba8d96584f5'
MODULE = 'DirectedFlowCutGap.FinalDispatchEnvelope'
DISPATCH_ORDER = ['FinalDispatchProgram','FinalDispatchCallLift','FinalDispatchCalls',
                  'FinalDispatchPrefix','FinalDispatchOutput','FinalDispatchPositive',
                  'FinalDispatchTail','FinalDispatchTrace','ActualFinalDispatch']
DISPATCH_MODULES = ['DirectedFlowCutGap.'+name for name in DISPATCH_ORDER]
NEW_MODULES = set(DISPATCH_MODULES+[MODULE])
SOURCE = ROOT/'DirectedFlowCutGap/FinalDispatchEnvelope.lean'
SMOKE = ROOT/'verification/FinalDispatchEnvelopeSmoke.lean'
AUDIT = ROOT/'verification/FinalDispatchEnvelopeFullRootValidation.lean'
BASELINE_SOURCE = PAPER/'verification/GridEnvelopeFullRootValidation.lean'
BASELINE_LOG = REBUILD/'logs/recovered-baseline722.log'
BASELINE_RECEIPT = REBUILD/'logs/recovered-baseline722.json'
STRICT_FLAGS = ['-j1','-DautoImplicit=false','-DwarningAsError=true']
ROOT_NAMES = ['fields_bits','vertex_word_bits','matrix_cells','empty_le_eval','avoiding_le_eval',
              'dispatch_le_eval','minimum_le_eval','original_le_eval','input_bound_exact',
              'instruction_le_eval','physical_eval','physical_le_eval','fixed_polynomial_bound',
              'solve_fixed_polynomial_bit']
SMOKE_NAMES = ['empty','singleton-no-demands','singleton-self-demand',
               'padded-zero-repeated-demands','padded-half-dense','mixed-sparse','four-rationals']

class Blocked(RuntimeError):
    pass


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        while data := f.read(1024*1024):
            h.update(data)
    return h.hexdigest()


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary = path.with_name(path.name+'.tmp-'+uuid.uuid4().hex)
    temporary.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    os.replace(temporary,path)


def rel(module: str, suffix: str) -> Path:
    return Path(*module.split('.')).with_suffix(suffix)


def need(condition: bool, message: str) -> None:
    if not condition:
        raise Blocked(message)


class Snapshot:
    """Hash each input once during preflight, and independently after the gate."""
    def __init__(self):
        self.files: dict[str,str] = {}

    def add(self, path: Path, expected: str | None = None) -> str:
        path = path.absolute()
        key = str(path)
        if key not in self.files:
            need(path.is_file(),'Missing input: '+key)
            self.files[key] = sha(path)
        actual = self.files[key]
        if expected is not None:
            need(actual==expected,'Input hash mismatch: '+key)
        return actual

    def verify(self) -> list[str]:
        changed = []
        for path,expected in self.files.items():
            try:
                if sha(Path(path))!=expected:
                    changed.append(path)
            except OSError:
                changed.append(path)
        return changed


def source_path(module: str) -> Path:
    if module==MODULE:
        return SOURCE
    return (DISPATCH if module in DISPATCH_MODULES else PAPER)/rel(module,'.lean')


def imports(path: Path) -> list[str]:
    return [word for line in re.findall(r'^import\s+([^\n]+)',path.read_text(),re.M)
            for word in line.split() if word.startswith('DirectedFlowCutGap.')]


def import_closure(module: str, known: set[str]) -> set[str]:
    done,visiting = set(),set()
    def visit(name):
        if name in done:
            return
        need(name in known,'Unknown production import: '+name)
        need(name not in visiting,'Production import cycle: '+name)
        visiting.add(name)
        for dep in imports(source_path(name)):
            visit(dep)
        visiting.remove(name)
        done.add(name)
    visit(module)
    return done-{module}


def load_environment(inputs: Snapshot) -> dict[str,str]:
    for filename in ['env.sh','project-env.sh']:
        inputs.add(TOOLCHAIN/filename)
    # This shell loads the prescribed recovered environment. It does not probe Lean.
    raw = subprocess.check_output(['bash','--noprofile','--norc','-c',
        'set -eu; source "$1/env.sh"; source "$1/project-env.sh"; env -0',
        'bash',str(TOOLCHAIN)],timeout=15)
    env = dict(x.split('=',1) for x in raw.decode().split('\0') if x)
    dependencies = env['FORMALIZATION_DEPENDENCY_LEAN_PATH'].split(':')
    need(all(not (Path(p)/'DirectedFlowCutGap').exists() for p in dependencies),
         'External dependency search root shadows DirectedFlowCutGap')
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_PATH'] = ':'.join([str(LIB),*dependencies])
    env['LEAN_SRC_PATH'] = ':'.join([str(ROOT),str(DISPATCH),str(PAPER),
                                    env['FORMALIZATION_DEPENDENCY_SRC_PATH']])
    expected = TOOLCHAIN/'lean-4.34.0-linux/bin/lean'
    need(Path(env['LEAN'])==expected,'Unexpected recovered Lean executable')
    inputs.add(expected)
    inputs.add(TOOLCHAIN/'lean-4.34.0-linux/bin/leanchecker')
    return env


def runtime_paths(env: dict[str,str]) -> list[str]:
    """The same runtime boundary used by the freshly pinned722 baseline."""
    roots = [Path(p) for p in env['FORMALIZATION_DEPENDENCY_LEAN_PATH'].split(':')]
    roots.append(TOOLCHAIN/'lean-4.34.0-linux/lib')
    paths = set()
    for root in roots:
        # Match the official pinned-baseline boundary: configured optional
        # dependency roots may be absent (for example Cli with no build output).
        # A newly appearing loadable file still changes the exact inventory.
        if not root.exists():
            continue
        need(root.is_dir(),'Runtime search root is not a directory: '+str(root))
        for path in root.rglob('*'):
            if path.is_file() and (path.name.endswith(('.olean','.olean.private','.olean.server','.ir','.so'))
                                   or '.so.' in path.name):
                paths.add(str(path.resolve()))
    paths.update(str(p) for p in [Path(env['LEAN']),TOOLCHAIN/'lean-4.34.0-linux/bin/leanchecker',
        TOOLCHAIN/'env.sh',TOOLCHAIN/'project-env.sh',TOOLCHAIN/'metadata/lake-manifest.json',
        REBUILD/'check_pinned_baseline.py'])
    return sorted(paths)


def pin_runtime(inputs: Snapshot, env: dict[str,str]) -> list[str]:
    inputs.add(BASELINE_RECEIPT)
    receipt = read_json(BASELINE_RECEIPT)
    need(receipt.get('returncode')==0 and receipt.get('inputs_unchanged') is True and
         receipt.get('runtime_files_unchanged') is True,
         'Fresh baseline has no successful unchanged runtime binding')
    need(receipt.get('lean_sysroot')==env.get('LEAN_SYSROOT') and
         receipt.get('dependency_lean_path')==env['FORMALIZATION_DEPENDENCY_LEAN_PATH'],
         'Runtime search boundary differs from fresh pinned722 baseline')
    paths = runtime_paths(env)
    need(paths==sorted(receipt['runtime_files']),
         'Official/dependency runtime inventory differs from fresh pinned722 baseline')
    for filename,expected in receipt['runtime_files'].items():
        inputs.add(Path(filename),expected)
    return paths


def baseline_bindings(inputs: Snapshot) -> tuple[dict,dict]:
    plan_path = REBUILD/'rebuild-plan.json'
    receipts_path = REBUILD/'object-receipts.json'
    inputs.add(plan_path)
    inputs.add(receipts_path)
    plan,receipts = read_json(plan_path),read_json(receipts_path)
    need(plan['commit']==BASE_COMMIT and len(plan['sources'])==722,
         'Rebuild plan does not describe the exact published722 baseline')
    commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE,text=True,timeout=15).strip()
    need(commit==BASE_COMMIT,'Published checkout commit changed')
    bindings = {}
    for module,expected in sorted(plan['sources'].items()):
        src,obj = source_path(module),REBUILD/'lib'/rel(module,'.olean')
        receipt = receipts.get(module)
        need(receipt is not None and receipt.get('returncode')==0 and receipt.get('source_unchanged'),
             'Published722 module lacks a successful rebuild receipt: '+module)
        need(receipt['source_sha256']==expected,'Published722 source receipt differs from plan: '+module)
        src_hash = inputs.add(src,expected)
        obj_hash = inputs.add(obj,receipt['olean_sha256'])
        bindings[module] = {'kind':'published722_rebuilt','source':str(src),'source_sha256':src_hash,
                            'object':str(obj),'object_sha256':obj_hash}
    return plan,bindings


def dispatcher_bindings(inputs: Snapshot, base: dict) -> dict:
    state_path = DISPATCH/'strict-build/state.json'
    inputs.add(state_path)
    state = read_json(state_path)
    bindings = dict(base)
    known = set(base)|set(DISPATCH_MODULES)
    for module in DISPATCH_MODULES:
        record = state.get('successes',{}).get(module)
        need(record is not None,'Dispatcher has no successful strict receipt: '+module)
        receipt_path = Path(record['receipt'])
        inputs.add(receipt_path,record['receipt_sha256'])
        receipt = read_json(receipt_path)
        need(receipt.get('module')==module and receipt.get('status')=='success' and
             receipt.get('returncode')==0,'Invalid dispatcher strict receipt: '+module)
        need(receipt.get('threads')==1 and set(STRICT_FLAGS)<=set(receipt.get('command',[])),
             'Dispatcher strict flags differ: '+module)
        need(all(receipt.get(key) is True for key in ['source_unchanged','imports_unchanged',
             'environment_unchanged','lean_executable_unchanged']),
             'Dispatcher strict postflight was not unchanged: '+module)
        src,obj = source_path(module),DISPATCH/'strict-build/lib'/rel(module,'.olean')
        need(Path(receipt['source'])==src and Path(receipt['output_object'])==obj,
             'Dispatcher receipt targets a different production file: '+module)
        need(not obj.is_symlink(),'Dispatcher production object must be real: '+module)
        src_hash = inputs.add(src,receipt['source_sha256'])
        inputs.add(Path(receipt['source_snapshot']),src_hash)
        obj_hash = inputs.add(obj,receipt['output_object_sha256'])
        inputs.add(Path(receipt['output_candidate']),obj_hash)
        log = Path(receipt['log'])
        inputs.add(log,receipt['log_sha256'])
        for path,expected in receipt['environment_scripts'].items():
            inputs.add(Path(path),expected)
        inputs.add(Path(receipt['lean_executable']),receipt['lean_executable_sha256'])
        expected_imports = import_closure(module,known)
        need(set(receipt['imports'])==expected_imports,'Dispatcher strict import closure changed: '+module)
        for name,binding in receipt['imports'].items():
            current = bindings.get(name)
            need(current is not None,'Dispatcher import lacks a bound predecessor: '+name)
            need(binding['source_sha256']==current['source_sha256'] and
                 binding['object_sha256']==current['object_sha256'],
                 'Dispatcher import binding changed: '+module+' -> '+name)
            if name in DISPATCH_MODULES:
                need(binding.get('successful_receipt_sha256')==current['successful_receipt_sha256'] and
                     binding.get('successful_log_sha256')==current['successful_log_sha256'],
                     'Dispatcher imported strict evidence changed: '+module+' -> '+name)
        bindings[module] = {'kind':'new_dispatcher_strict','source':str(src),'source_sha256':src_hash,
                            'object':str(obj),'object_sha256':obj_hash,
                            'successful_receipt':str(receipt_path),
                            'successful_receipt_sha256':inputs.add(receipt_path),
                            'successful_log':str(log),'successful_log_sha256':inputs.add(log)}
    return bindings


def state() -> dict:
    path = BUILD/'state.json'
    return read_json(path) if path.exists() else {'successes':{},'latest_attempts':{}}


def require_gate(inputs: Snapshot, mode: str, envelope_hash: str | None = None) -> dict:
    entry = state().get('successes',{}).get(mode)
    need(entry is not None,'No successful envelope '+mode+' gate exists')
    path = Path(entry['receipt'])
    inputs.add(path,entry['receipt_sha256'])
    receipt = read_json(path)
    need(receipt.get('gate')==mode and receipt.get('status')=='success' and
         receipt.get('returncode')==0 and receipt.get('inputs_unchanged') is True,
         'Invalid successful envelope '+mode+' receipt')
    need(receipt.get('module')==MODULE,'Successful gate belongs to another production module')
    for filename,expected in receipt['input_artifacts'].items():
        inputs.add(Path(filename),expected)
    obj = LIB/rel(MODULE,'.olean')
    need(not obj.is_symlink(),'Envelope production object must be real')
    object_hash = inputs.add(obj,receipt['envelope_object_sha256'])
    inputs.add(Path(receipt['log']),receipt['log_sha256'])
    inputs.add(SOURCE,receipt['production_source_sha256'])
    if envelope_hash is not None:
        need(object_hash==envelope_hash,'Gate receipt refers to another envelope object')
    if mode=='strict':
        need(set(STRICT_FLAGS)<=set(receipt.get('command',[])) and receipt.get('threads')==1,
             'Envelope strict receipt lacks required flags')
        inputs.add(Path(receipt['output_candidate']),object_hash)
    if mode=='replay':
        expected = [str(TOOLCHAIN/'lean-4.34.0-linux/bin/leanchecker'),'-v',MODULE]
        need(receipt['command']==expected and receipt.get('threads')==1,
             'Replay did not use the official bound single-module leanchecker command')
    return {'receipt':str(path),'receipt_sha256':inputs.add(path),'log':receipt['log'],
            'log_sha256':receipt['log_sha256'],'envelope_object_sha256':object_hash}


def overlay(bindings: dict) -> None:
    """One flattened namespace: parent and dispatcher symlinks, real envelope."""
    namespace = LIB/'DirectedFlowCutGap'
    namespace.mkdir(parents=True,exist_ok=True)
    expected = {}
    for module,binding in bindings.items():
        target = Path(binding['object'])
        # These are classic modules. Reject unbound server/private parts, which
        # official leanchecker would otherwise load alongside the bound object.
        for suffix in ['.server','.private']:
            need(not Path(str(target)+suffix).exists(),'Unexpected unbound object part: '+str(target)+suffix)
        dest = LIB/rel(module,'.olean')
        expected[dest] = target
        dest.parent.mkdir(parents=True,exist_ok=True)
        if dest.is_symlink():
            need(dest.resolve()==target.resolve(),'Wrong overlay symlink target: '+str(dest))
        else:
            need(not dest.exists(),'Imported overlay slot is not a symlink: '+str(dest))
            dest.symlink_to(target)
    own = LIB/rel(MODULE,'.olean')
    for item in namespace.rglob('*'):
        if item.is_dir():
            continue
        need(item in expected or (item==own and not item.is_symlink()),
             'Unknown or diagnostic object in production namespace: '+str(item))


def parse_attribution(text: str) -> dict[str,str]:
    owners = {}
    for module,name in re.findall(r'^ATTR ([^|\n]+)\|([^\n]+)$',text,re.M):
        need(name not in owners,'Duplicate attributed name: '+name)
        owners[name] = module
    return owners


def fresh_baseline(inputs: Snapshot, base: dict) -> dict[str,str]:
    inputs.add(BASELINE_RECEIPT)
    receipt = read_json(BASELINE_RECEIPT)
    need(receipt.get('returncode')==0 and receipt.get('inputs_unchanged') is True,
         'Fresh baseline gate did not finish successfully with unchanged inputs')
    need(Path(receipt['source'])==BASELINE_SOURCE and Path(receipt['log'])==BASELINE_LOG,
         'Fresh baseline receipt refers to unexpected source/log')
    inputs.add(BASELINE_SOURCE,receipt['source_sha256'])
    inputs.add(BASELINE_LOG,receipt['log_sha256'])
    need(set(receipt['modules'])==set(base),'Fresh baseline receipt does not bind exactly722 modules')
    for module,binding in receipt['modules'].items():
        need(binding['source_sha256']==base[module]['source_sha256'] and
             binding['object_sha256']==base[module]['object_sha256'],
             'Fresh baseline source/object binding is stale: '+module)
    text = BASELINE_LOG.read_text()
    owners = parse_attribution(text)
    need(len(owners)==26090 and set(owners.values())==set(base),
         'Fresh baseline does not expose26090 names across exactly722 modules')
    need(len(re.findall(r'^GRID_ENVELOPE_TYPE_BODY_CLOSURE passed:',text,re.M))==14,
         'Fresh baseline lacks14 old full-root closure passes')
    need(len(re.findall(r'^PASS numerical (?:original-input|controller) envelope ',text,re.M))==12,
         'Fresh baseline lacks12 numerical-only passes')
    return owners


def semantic_gate_check(mode: str, log: Path, attempt: Path, base: dict,
                        old_owners: dict[str,str] | None) -> dict:
    text = log.read_text()
    if mode=='strict':
        return {'scope':'Strict production module elaboration only'}
    if mode=='replay':
        lines = re.findall(r'^replaying (.+)$',text,re.M)
        need(lines==[MODULE],'Official replay did not report exactly the final envelope module')
        return {'official_kernel_replayed_module':MODULE}
    if mode=='smoke':
        names = re.findall(r'^PASS numerical final-dispatch envelope (\S+) ',text,re.M)
        need(names==SMOKE_NAMES,'Seven expected numerical smoke cases did not all pass in order')
        return {'numerical_only_cases':names,'physical_fixture_count':0}
    owners = parse_attribution(text)
    need(set(owners.values())==set(base)|NEW_MODULES,
         'New full audit does not attribute every722+10 production module')
    module_passes = re.findall(r'^FINAL_DISPATCH_ENVELOPE_MODULE_AUDIT passed: ([^;]+); (\d+) declarations$',text,re.M)
    need(len(module_passes)==10 and {m for m,_ in module_passes}==NEW_MODULES and
         all(int(n)>0 for _,n in module_passes),'New-module audit does not pass exactly10 modules')
    roots = re.findall(r'^FINAL_DISPATCH_ENVELOPE_TYPE_BODY_CLOSURE passed: ([^;]+);',text,re.M)
    expected_roots = [MODULE+'.'+root for root in ROOT_NAMES]
    need(roots==expected_roots,'Fourteen selected complete type/body closures did not all pass')
    need(old_owners is not None,'Fresh baseline names were not loaded')
    missing = sorted(set(old_owners)-set(owners))
    additions = sorted(set(owners)-set(old_owners))
    shifts = [{'name':name,'old_owner':old_owners[name],'new_owner':owners[name]}
              for name in sorted(set(old_owners)&set(owners)) if old_owners[name]!=owners[name]]
    invalid = [{'name':name,'owner':owners[name]} for name in additions if owners[name] not in NEW_MODULES]
    comparison = {'baseline_kind':'fresh replay of unchanged published722 validator; no lost log recovered',
                  'baseline_names':len(old_owners),'current_names':len(owners),
                  'missing_old_names':missing,'additions':[{'name':n,'owner':owners[n]} for n in additions],
                  'invalid_addition_owners':invalid,'ownership_shifts':shifts}
    attribution = attempt/'declaration-attribution.json'
    comparison_path = attempt/'old-name-preservation.json'
    write_json(attribution,{'names':owners,'count':len(owners)})
    write_json(comparison_path,comparison)
    need(not missing,'Audit lost published722 declaration names; see '+str(comparison_path))
    need(not invalid,'New declaration has an owner outside the10 new modules; see '+str(comparison_path))
    return {'old_names_preserved':len(old_owners),'addition_count':len(additions),
            'ownership_shift_count':len(shifts),'full_type_body_closures':len(roots),
            'attribution':str(attribution),'attribution_sha256':sha(attribution),
            'comparison':str(comparison_path),'comparison_sha256':sha(comparison_path)}


def run(args) -> int:
    ident = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'-'+uuid.uuid4().hex[:8]
    attempt = BUILD/'attempts'/ident/args.mode
    attempt.mkdir(parents=True,exist_ok=False)
    log,receipt_path = attempt/'gate.log',attempt/'receipt.json'
    log.write_text('')
    started = time.monotonic()
    deadline = started+args.seconds
    r = {'gate':args.mode,'module':MODULE,'status':'preflight','started_at':utc(),
         'log':str(log),'lock':str(LOCK),'threads':1,'returncode':None,'auto_retry':False,
         'physical_fixture_count':0,'input_artifacts':{},'inputs_unchanged':False,
         'scope':'Only this explicitly named local gate; no publication, CI, or physical-fixture claim'}
    inputs = Snapshot()
    lock,acquired,proc = None,False,None
    runtime_before,env = None,None
    try:
        lock = LOCK.open('a')
        lock_deadline = min(deadline,time.monotonic()+args.lock_wait)
        while True:
            try:
                fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
                acquired = True
                break
            except BlockingIOError:
                need(time.monotonic()<lock_deadline,'Compiler lock is busy; no validation process launched')
                time.sleep(.1)
        r['lock_acquired_at'] = utc()
        inputs.add(Path(__file__))
        plan,base = baseline_bindings(inputs)
        bindings = dispatcher_bindings(inputs,base)
        env = load_environment(inputs)
        runtime_before = pin_runtime(inputs,env)
        r['official_dependency_runtime_files'] = len(runtime_before)
        r['pinned_runtime_baseline_receipt'] = str(BASELINE_RECEIPT)
        r['pinned_runtime_baseline_receipt_sha256'] = inputs.add(BASELINE_RECEIPT)
        r['production_source_sha256'] = inputs.add(SOURCE)
        r['production_source'] = str(SOURCE)
        r['baseline_commit'] = plan['commit']
        r['modules'] = bindings
        r['lean_path'] = env['LEAN_PATH']
        r['successful_dispatcher_strict_evidence'] = {m:{k:v for k,v in bindings[m].items()
            if k.startswith('successful_')} for m in DISPATCH_MODULES}
        overlay(bindings)
        old_owners = None
        if args.mode!='strict':
            r['envelope_strict'] = require_gate(inputs,'strict')
            r['envelope_object_sha256'] = r['envelope_strict']['envelope_object_sha256']
        if args.mode in ['smoke','audit']:
            r['envelope_replay'] = require_gate(inputs,'replay',r['envelope_object_sha256'])
        if args.mode=='audit':
            old_owners = fresh_baseline(inputs,base)
            r['fresh_baseline_receipt'] = str(BASELINE_RECEIPT)
            r['fresh_baseline_receipt_sha256'] = inputs.add(BASELINE_RECEIPT)
        if args.mode=='replay':
            cmd = [str(TOOLCHAIN/'lean-4.34.0-linux/bin/leanchecker'),'-v',MODULE]
            cwd = attempt
        else:
            original = {'strict':SOURCE,'smoke':SMOKE,'audit':AUDIT}[args.mode]
            expected = inputs.add(original)
            source_rel = rel(MODULE,'.lean') if args.mode=='strict' else Path('verification')/original.name
            snapshot = attempt/'source'/source_rel
            snapshot.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(original,snapshot)
            inputs.add(snapshot,expected)
            r['gate_source'] = str(original)
            r['gate_source_sha256'] = expected
            r['source_snapshot'] = str(snapshot)
            cmd = [env['LEAN'],*STRICT_FLAGS]
            if args.mode=='strict':
                output = attempt/'output'/rel(MODULE,'.olean')
                output.parent.mkdir(parents=True,exist_ok=True)
                cmd.extend(['-o',str(output)])
                r['output_candidate'] = str(output)
            cmd.append(str(source_rel))
            cwd = attempt/'source'
        cap = deadline-time.monotonic()
        need(cap>0,'Gate wall budget exhausted during preflight; no Lean/checker launched')
        r.update(command=cmd,cwd=str(cwd),cap_seconds=cap,status='running',input_artifacts=dict(inputs.files))
        write_json(receipt_path,r)
        with log.open('wb') as output_log:
            proc = subprocess.Popen(cmd,cwd=cwd,env=env,stdout=output_log,stderr=subprocess.STDOUT,
                                    start_new_session=True,pass_fds=(lock.fileno(),))
            try:
                r['returncode'] = proc.wait(timeout=cap)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL)
                proc.wait()
                r['returncode'] = 124
        changed = inputs.verify()
        r['changed_inputs'] = changed
        r['runtime_inventory_unchanged'] = runtime_paths(env)==runtime_before
        r['inputs_unchanged'] = not changed and r['runtime_inventory_unchanged']
        # Verify overlay names/targets again, without allowing a different search
        # root to supply a hidden replacement production object.
        overlay(bindings)
        if r['returncode']==124:
            r['status'] = 'capped'
        elif r['returncode']!=0:
            r['status'] = 'failed'
        elif not r['inputs_unchanged']:
            r['status'] = 'binding_changed'
        else:
            r['checks'] = semantic_gate_check(args.mode,log,attempt,base,old_owners)
            if args.mode=='strict':
                candidate = Path(r['output_candidate'])
                need(candidate.is_file(),'Strict compile returned0 without its production object')
                for suffix in ['.server','.private']:
                    need(not Path(str(candidate)+suffix).exists(),'Unbound strict object sidecar produced')
                dest = LIB/rel(MODULE,'.olean')
                need(not dest.is_symlink(),'Envelope production slot unexpectedly is a symlink')
                temp = dest.with_name(dest.name+'.tmp-'+ident)
                shutil.copyfile(candidate,temp)
                os.replace(temp,dest)
                r['envelope_object'] = str(dest)
                r['envelope_object_sha256'] = sha(dest)
                need(sha(candidate)==r['envelope_object_sha256'],'Published envelope differs from retained strict object')
            r['status'] = 'success'
    except BaseException as error:
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid,signal.SIGKILL)
            proc.wait()
        r['status'] = 'blocked' if r['returncode'] is None else 'postflight_failed'
        r['error'] = str(error)
        if inputs.files:
            r['changed_inputs'] = inputs.verify()
            r['inputs_unchanged'] = not r['changed_inputs']
            if runtime_before is not None and env is not None:
                r['runtime_inventory_unchanged'] = runtime_paths(env)==runtime_before
                r['inputs_unchanged'] = r['inputs_unchanged'] and r['runtime_inventory_unchanged']
        if args.mode=='strict':
            r.pop('envelope_object_sha256',None)
    finally:
        # Recheck again after semantic parsing/publication and before sealing the
        # receipt. Even capped/failed gates retain the final unchanged verdict.
        if inputs.files:
            final_changes = inputs.verify()
            r['changed_inputs'] = final_changes
            r['inputs_unchanged'] = not final_changes
            if runtime_before is not None and env is not None:
                r['runtime_inventory_unchanged'] = runtime_paths(env)==runtime_before
                r['inputs_unchanged'] = r['inputs_unchanged'] and r['runtime_inventory_unchanged']
            if not r['inputs_unchanged'] and r['status']=='success':
                r['status'] = 'binding_changed'
                if args.mode=='strict':
                    r.pop('envelope_object_sha256',None)
        r['input_artifacts'] = dict(inputs.files)
        r['ended_at'] = utc()
        r['elapsed_seconds'] = time.monotonic()-started
        r['log_sha256'] = sha(log)
        write_json(receipt_path,r)
        if acquired:
            current = state()
            entry = {'receipt':str(receipt_path),'receipt_sha256':sha(receipt_path)}
            current['latest_attempts'][args.mode] = entry
            if r['status']=='success':
                current['successes'][args.mode] = entry
            write_json(BUILD/'state.json',current)
            fcntl.flock(lock,fcntl.LOCK_UN)
        if lock is not None:
            lock.close()
    print(json.dumps({'gate':args.mode,'status':r['status'],'returncode':r['returncode'],
                      'receipt':str(receipt_path),'receipt_sha256':sha(receipt_path),
                      'elapsed_seconds':r['elapsed_seconds'],'error':r.get('error')},indent=2),flush=True)
    return 0 if r['status']=='success' else 2


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['strict','replay','smoke','audit'])
    parser.add_argument('--seconds',type=float,default=None,
                        help='Total gate preflight+process budget, max1800 seconds; postflight always runs')
    parser.add_argument('--lock-wait',type=float,default=5,help='Bounded exclusive-lock wait, max600 seconds')
    args = parser.parse_args()
    if args.seconds is None:
        args.seconds = {'strict':180,'replay':300,'smoke':120,'audit':600}[args.mode]
    if not 0<args.seconds<=1800 or not 0<args.lock_wait<=600:
        parser.error('Budgets must be positive; seconds≤1800 and lock-wait≤600')
    return run(args)


if __name__=='__main__':
    sys.exit(main())
