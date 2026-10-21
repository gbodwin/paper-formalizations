"""Twelve bounded batch children, consuming only authenticated same-run producers."""
from pathlib import Path
import hashlib, json, os, subprocess, sys, time, traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ENGINE = ROOT / 'checkpoints/light-eft-canonical-output-adapter-20261020'
FLAGS = ['-j1', '-s65536', '-M5120', '-DautoImplicit=false', '-DwarningAsError=true']

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def load(path):
    return json.loads(Path(path).read_text())

def save(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n')

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

def bound_spec():
    path = HERE / 'ci-spec.json'
    raw = subprocess.check_output(['git', 'show', 'HEAD:' + str(path.relative_to(ROOT))], cwd=ROOT)
    require(path.read_bytes() == raw, 'Bridge specification differs from exact checkout')
    spec = json.loads(raw)
    for row in [*spec['sources'], *spec['dependencies'], *spec['engine_files']]:
        rel = Path(row['path'])
        require(not rel.is_absolute() and '..' not in rel.parts, 'Unsafe bound bridge path')
        p = ROOT / rel
        require(not any(q.is_symlink() for q in [p, *p.parents]), 'Symlink bound bridge source')
        require(p.is_file() and p.stat().st_size == row['bytes'] and digest(p) == row['sha256'], 'Bridge source byte binding changed: ' + str(rel))
        require(subprocess.check_output(['git', 'show', 'HEAD:' + str(rel)], cwd=ROOT) == p.read_bytes(), 'Bound bridge input differs from Git HEAD')
    return spec

def build_plans(tool, work, spec, roots, head, bind):
    from finite_contract import CONTRACT
    sources = {r['role']: ROOT / r['path'] for r in spec['sources']}
    staged = list(dict.fromkeys(ROOT / spec['source_roots'][m] for m in CONTRACT['modules']))
    env = dict(LANG='C.UTF-8', LC_ALL='C.UTF-8', LEAN_NUM_THREADS='1', LEAN_SYSROOT=str(tool),
        LEAN_PATH=':'.join(map(str, roots)),
        LEAN_SRC_PATH=':'.join(map(str, [*staged, *[ROOT / p for p in spec['dependency_staged_roots']], ROOT / 'Light Edge Fault Tolerant Graph Spanners', ROOT / 'An Alternate Proof of Near-Optimal Light Spanners', tool / 'src/lean'])),
        MIMALLOC_ARENA_RESERVE='128MiB', MIMALLOC_VERBOSE='1', LIGHTEFT_SOURCE_COMMIT=head,
        LIGHTEFT_HARNESS_COMMIT=head, LIGHTEFT_FROZEN_SOURCE_COMMIT='78cb40c7837db049d645d73696f2e0b724ce8a3b')
    result = []
    for module, role in zip(CONTRACT['modules'], ['flat','sampler','independent'], strict=True):
        case = module.rsplit('.',1)[-1]
        proof, audit, resolver = sources[role], sources[role+'_audit'], sources['resolver']
        target = work / 'objects' / Path(*module.split('.')).with_suffix('.olean')
        commands = [[str(tool / 'bin/lean'), *FLAGS, '--root=' + str(ROOT / spec['source_roots'][module]), '-o', str(target), str(proof)],
            [str(tool / 'bin/lean'), *FLAGS, str(resolver)], [str(tool / 'bin/leanchecker'), '-v', module],
            [str(tool / 'bin/lean'), *FLAGS, str(audit)]]
        for kind, argv, submitted in zip(['compile','resolve','replay','audit'], commands, [[proof],[resolver,proof],[proof],[audit,proof]], strict=True):
            e = env.copy()
            if kind == 'resolve': e.update(LIGHTEFT_CHECKER_TARGET=module, LIGHTEFT_CHECKER_RESOLUTION_FILE=str(work/'resolution'/(case+'.json')))
            if kind == 'replay': e.pop('MIMALLOC_VERBOSE'); e['LEAN_STACK_SIZE_KB']='65536'
            require(len(json.dumps(dict(argv=argv,env=e,stage=kind)).encode()) <= 4096, 'Accepted launcher configuration bound exceeded')
            p = dict(stage=kind,module=module,case=case,argv=argv,env=e,sources=list(map(str,submitted)),cwd=str(work/'audit'/case if kind=='audit' else work))
            p['source_bindings'] = [bind(x) for x in p['sources']]
            result.append(p)
    return result

def execute_sequence(plans, child, finish):
    from finite_contract import CONTRACT
    expected = [(m,s) for m in CONTRACT['modules'] for s in ['compile','resolve','replay','audit']]
    require([(p['module'],p['stage']) for p in plans] == expected, 'Batch schedule differs')
    stages=[]
    for p in plans:
        receipt=child(p)
        stages.append(dict(module=p['module'],stage=p['stage'],attempt_id=receipt['attempt_id']))
    return dict(stages=stages,result=finish())

def boundary_inputs(spec, roots, semantic, bind):
    from package_selection import selected_path
    from finite_contract import CONTRACT
    result = {}
    rows = spec['external_boundary_sources']
    require(rows == CONTRACT['external_boundary_sources'] and len(rows) == len({r['module'] for r in rows}) == 30, 'External source boundary differs')
    for row in rows:
        module = row['module']
        require(row['package'] in spec['pins'] and row['package_commit'] == spec['pins'][row['package']], 'Boundary source package pin differs')
        primary = ROOT / row['object']
        matches = [Path(root) / Path(*module.split('.')).with_suffix('.olean') for root in roots]
        require([p for p in matches if p.exists() or p.is_symlink()] == [primary] and selected_path(roots, module) == primary, 'Boundary object missing/shadowed/masked')
        require(str(primary) in semantic and bind(primary) == semantic[str(primary)], 'Boundary object is not a sealed semantic input')
        source = ROOT / row['source']
        package = ROOT / '.lake/packages' / row['package']
        raw = subprocess.check_output(['git', '-C', str(package), 'show', 'HEAD:' + str(source.relative_to(package))])
        require(source.read_bytes() == raw and len(raw)==row['source_bytes'] and hashlib.sha256(raw).hexdigest()==row['source_sha256'], 'Boundary source differs from exact pinned binding')
        result[str(source)] = bind(source)
    return result

def finite_scope(spec):
    from finite_contract import CONTRACT
    mods=CONTRACT['modules']
    require(len(mods)==len(set(mods))==3, 'Exactly three batch modules required')
    names=[r['module'] for r in spec['dependencies']]
    require(len(names)==len(set(names))==81, 'Exactly81 inherited project sources required')
    for i,m in enumerate(mods):
        require(set(CONTRACT['imports'][m])==set(names)|set(mods[:i]) and len(CONTRACT['imports'][m])==81+i,'Exact per-module import set differs')
    origins={r['module']:r['origin'] for r in spec['dependencies']}
    require(sorted(origins.values())==sorted(['ordinary_build']*77+['paid']*2+['decoder','bridge']), 'Batch origin split differs')
    require({m:o for m,o in origins.items() if o!='ordinary_build'}==CONTRACT['staged_origins'], 'Staged origins differ')
    expected=list(dict.fromkeys(r['path'].split('/staged/',1)[0]+'/staged' for r in spec['dependencies'] if r['origin']!='ordinary_build'))
    require(spec['dependency_staged_roots']==expected, 'Staged source roots differ')
    roles=['flat','sampler','independent']
    require(len(spec['sources'])==7 and {r['role'] for r in spec['sources']}==set(roles+[r+'_audit' for r in roles]+['resolver']), 'Batch source roles differ')
    for m,role in zip(mods,roles,strict=True):
        proof=next(r for r in spec['sources'] if r['role']==role)
        require({k:proof[k] for k in ['path','bytes','sha256']}==CONTRACT['reviewed_sources'][m], 'Reviewed mathematical source differs')
        require(spec['source_roots'][m]==proof['path'].split('/staged/',1)[0]+'/staged', 'Proof source root differs')
    require(spec['resource_contract']==CONTRACT['resources'] and spec['execution_order']==[[m,s] for m in mods for s in ['compile','resolve','replay','audit']], 'Resource/schedule metadata differs')
    require(spec['pins']==CONTRACT['pins'] and spec['tool_hashes']==CONTRACT['tool_hashes'] and spec['toolchain']=='leanprover/lean4:v4.34.0', 'Pins/tools differ')
    require(spec['external_boundary_sources']==CONTRACT['external_boundary_sources'] and len(spec['external_boundary_sources'])==30,'External boundary differs')
    require(spec['required_roots']==CONTRACT['required_roots'] and spec['required_interfaces']==CONTRACT['interfaces'], 'Declaration/interface scope differs')
    require([len(spec['required_roots'][m]) for m in mods]==[10,20,6], 'All36 required theorem roots not bound')
    require(spec['project_counts']=={m:dict(imports=81+i,including_target=82+i) for i,m in enumerate(mods)}, 'Per-target counts differ')
    return set(names),origins

def verify_schedule(plans, evidence, lease, context, handoff, identity, verify_receipts):
    from finite_contract import CONTRACT
    head=identity['GITHUB_SHA']
    for i,m in enumerate(CONTRACT['modules']):
        part=plans[i*4:i*4+4]
        verify_receipts(evidence/m.rsplit('.',1)[-1],lease,part,context.dependencies(part[0]),head,expected_source=head)
    ids=set(handoff['prior_attempt_ids']);previous=handoff['last_release_ns']
    require(len(ids)==17 and previous<lease['acquired_ns'], 'Producer/batch ownership boundary differs')
    for p in plans:
        r=load(evidence/p['case']/p['stage']/'receipt.json')
        require(r.get('CI_identity')==identity and r.get('workflow_job')=='check' and r.get('focused_module')==p['module'] and r.get('focused_case')==p['case'], 'Batch receipt identity differs')
        require(r['attempt_id'] not in ids and previous<r['started_ns']<r['ended_ns'], 'Duplicate or overlapping batch child')
        ids.add(r['attempt_id']);previous=r['ended_ns']
    require(len(ids)==29 and previous<=lease['release_ns'] and lease['state']=='released' and lease.get('kernel_echild') and not lease.get('release_errors'), 'Batch schedule/release incomplete')

def workflow_identity(env, head):
    from ci_policy import ci_identity
    identity = ci_identity(env, head)
    require(env.get('GITHUB_JOB') == 'check', 'Bridge must run in the single bound check job')
    return identity

def run_stage(root, env, spec):
    sys.path.insert(0, str(ENGINE))
    sys.path.insert(0, str(HERE))
    sys.path.insert(0, str(ROOT / 'scripts'))
    from finite_contract import CONTRACT
    from contracts import bind, save as durable_save
    from ci_inventory import CIInventory
    from ci_lease import CILease
    from ci_accounting import CIAccounting
    from ci_receipts import verify_receipts
    from ci_admission_receipts import verify_singleton_receipt
    from LightEFTCgroup import memory_snapshot
    from batch_context import FocusedContext
    import child_runner, audit_check, same_run
    head = git('rev-parse', 'HEAD')
    identity = workflow_identity(env, head)
    def identity_check():
        require(workflow_identity(dict(os.environ), head) == identity and
                os.environ.get('RUNNER_TEMP') == env['RUNNER_TEMP'], 'Bridge CI/job/temp identity drift')
    candidates = [p for p in (Path(env['HOME']) / '.elan/toolchains').iterdir() if (p / 'bin/lean').is_file() and digest(p / 'bin/lean') == spec['tool_hashes']['lean']]
    require(len(candidates) == 1, 'Exactly one accepted hash-pinned toolchain required')
    tool = candidates[0]
    require(digest(tool / 'bin/leanchecker') == spec['tool_hashes']['leanchecker'], 'Accepted checker hash differs')
    for name, revision in spec['pins'].items():
        folder = ROOT / '.lake/packages' / name
        require(git('-C', str(folder), 'rev-parse', 'HEAD') == revision and not git('-C', str(folder), 'status', '--porcelain', '--untracked-files=no'), 'Locked package source differs')
    names, origins = finite_scope(spec)
    packages = ROOT / '.lake/packages'
    normal = [ROOT / '.lake/build/lib/lean', *[packages / n / '.lake/build/lib/lean' for n in spec['pins'] if (packages / n / '.lake/build/lib/lean').is_dir()], tool / 'lib/lean']
    handoff = same_run.collect(ROOT, tool, env, identity, spec, normal, verify_receipts, verify_singleton_receipt)
    require({m for m in names if origins[m] != 'ordinary_build'} == set(handoff['staged']), 'Wrong staged origin set')
    work, evidence = root / 'work', root / 'runtime'
    require(not work.exists() and not evidence.exists(), 'Fresh bridge roots required')
    roots = [work / 'objects', handoff['bridge']['root'] / 'work/objects', handoff['paid']['root'] / 'work/objects', handoff['decoder']['root'] / 'work/objects', *normal]
    dependencies = {}
    for m in sorted(names):
        dependencies[m] = handoff['staged'][m] if m in handoff['staged'] else dict(bind(normal[0] / Path(*m.split('.')).with_suffix('.olean')), module=m)
    inventory = CIInventory(roots[1:], tool, bind)
    classified = inventory.scan()
    inputs = {**classified['semantic'], **handoff['protected']}
    inputs.update(boundary_inputs(spec, roots[1:], classified['semantic'], bind))
    for row in [*spec['sources'], *spec['dependencies'], *spec['engine_files']]:
        inputs[str(ROOT / row['path'])] = bind(ROOT / row['path'])
    for path in [HERE / 'ci-spec.json', ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain', tool / 'bin/lean', tool / 'bin/leanchecker']:
        inputs[str(path)] = bind(path)
    matched = same_run.retained(handoff, normal, classified, inputs)
    save(root / 'same-run-handoff.json', dict(CI_identity=identity, workflow_job='check', prior_attempt_ids=handoff['prior_attempt_ids'],
        paid_root=str(handoff['paid']['root']), decoder_root=str(handoff['decoder']['root']), bridge_root=str(handoff['bridge']['root']),
        producer_leases={k: handoff[k]['lease'] for k in ['paid', 'decoder', 'bridge']}, retained_context=matched,
        staged_objects=handoff['staged'], origins=origins, qualification=spec['dependency_qualification']))
    inputs[str(root / 'same-run-handoff.json')] = bind(root / 'same-run-handoff.json')
    plans = build_plans(tool, work, spec, roots, head, bind)
    save(root / 'plans.json', plans)
    identity_check()
    child_runner.assert_idle('bridge-before-claim', {})
    (root / 'production-claim.json').open('x').write(json.dumps(identity) + '\n')
    (work / 'objects' / CONTRACT['modules'][0].split('.')[0]).mkdir(parents=True)
    (work / 'resolution').mkdir()
    evidence.mkdir()
    state = dict(accepted=False, independent_review='pending', CI_identity=identity, workflow_job='check', source_commit=head, harness_commit=head,
                 dependency_qualification=spec['dependency_qualification'])
    try:
        with CILease(root, durable_save, identity_check) as lease:
            require(handoff['last_release_ns'] < lease.acquired_ns, 'Producer/new bridge leases overlap')
            context = FocusedContext(lease, work, evidence, plans, roots, dependencies, identity, inputs,
                                     inventory, classified, handoff['trees'], handoff['protected'])
            accounting = CIAccounting(memory_snapshot)
            def child(p):
                if p['stage']=='compile': context.target(p['module']).parent.mkdir(parents=True,exist_ok=True)
                r = child_runner.run_child(p, Path(p['cwd']), evidence / p['case'] / p['stage'], context, accounting=accounting)
                path = evidence / p['case'] / p['stage'] / 'receipt.json'
                context.evidence_files[str(path)] = bind(path)
                return r
            state.update(execute_sequence(plans, child, context.finish))
        verify_schedule(plans, evidence, lease.record, context, handoff, identity, verify_receipts)
        state['accepted'] = True
    except BaseException as error:
        state['failure'] = repr(error)
        traceback.print_exc()
    finally:
        save(root / 'result.json', state)
        exports = []
        for p in sorted(evidence.rglob('*')):
            if p.is_file() and p.name in ['raw.log', 'receipt.json', 'samples.jsonl', 'inputs.jsonl', 'excluded-metadata-initial.jsonl']:
                directory = root / 'available-exports' / p.relative_to(evidence)
                m = audit_check.chunk(p, directory)
                exports.append(dict(source=str(p), manifest=str(directory / 'manifest.json'), bytes=m['bytes'], sha256=m['sha256']))
        save(root / 'available-export-index.json', exports)
    return state

def main():
    env = dict(os.environ)
    require(env.get('GITHUB_RUN_ID', '').isdecimal() and env.get('GITHUB_RUN_ATTEMPT', '').isdecimal(), 'Ordinary CI identity required')
    temp = Path(env['RUNNER_TEMP'])
    require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(), 'Invalid runner temp')
    suffix = env['GITHUB_RUN_ID'] + '-' + env['GITHUB_RUN_ATTEMPT']
    cache = temp / ('light-eft-fair-bit-batch-python-' + suffix)
    require(sys.dont_write_bytecode and sys.pycache_prefix == str(cache) and not cache.exists(), 'Fresh absent -B Python cache prefix required')
    root = temp / ('light-eft-fair-bit-batch-' + suffix)
    root.mkdir(mode=0o700, exist_ok=False)
    try:
        require(run_stage(root, env, bound_spec())['accepted'], 'Fair-bit batch gate failed')
    except BaseException as error:
        save(root / 'stage-failure.json', dict(error=repr(error)))
        (root / 'stage-raw.log').write_text(traceback.format_exc())
        traceback.print_exc()
        return 1
    finally:
        rows = [dict(path=str(p.relative_to(root)), bytes=p.stat().st_size, sha256=digest(p))
                for p in sorted(root.rglob('*')) if p.is_file() and p.name != 'evidence-sha256.json']
        save(root / 'evidence-sha256.json', rows)
    return 0

if __name__ == '__main__':
    sys.exit(main())
