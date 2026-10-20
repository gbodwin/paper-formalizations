"""Four bounded bridge children, consuming only authenticated same-run producers."""
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
    module = CONTRACT['modules'][0]
    case = module.rsplit('.', 1)[-1]
    source = {r['role']: ROOT / r['path'] for r in spec['sources']}
    proof, resolver, audit = source['bridge'], source['resolver'], source['audit']
    staged = ROOT / spec['staged_root']
    env = dict(LANG='C.UTF-8', LC_ALL='C.UTF-8', LEAN_NUM_THREADS='1', LEAN_SYSROOT=str(tool),
        LEAN_PATH=':'.join(map(str, roots)),
        LEAN_SRC_PATH=':'.join(map(str, [staged, *[ROOT / p for p in spec['dependency_staged_roots']], ROOT / 'Light Edge Fault Tolerant Graph Spanners', ROOT / 'An Alternate Proof of Near-Optimal Light Spanners', tool / 'src/lean'])),
        MIMALLOC_ARENA_RESERVE='128MiB', MIMALLOC_VERBOSE='1', LIGHTEFT_SOURCE_COMMIT=head,
        LIGHTEFT_HARNESS_COMMIT=head, LIGHTEFT_FROZEN_SOURCE_COMMIT='78cb40c7837db049d645d73696f2e0b724ce8a3b')
    target = work / 'objects' / Path(*module.split('.')).with_suffix('.olean')
    commands = [[str(tool / 'bin/lean'), *FLAGS, '--root=' + str(staged), '-o', str(target), str(proof)],
        [str(tool / 'bin/lean'), *FLAGS, str(resolver)],
        [str(tool / 'bin/leanchecker'), '-v', module], [str(tool / 'bin/lean'), *FLAGS, str(audit)]]
    result = []
    for kind, argv, submitted in zip(['compile', 'resolve', 'replay', 'audit'], commands, [[proof], [resolver, proof], [proof], [audit, proof]], strict=True):
        e = env.copy()
        if kind == 'resolve':
            e.update(LIGHTEFT_CHECKER_TARGET=module, LIGHTEFT_CHECKER_RESOLUTION_FILE=str(work / 'resolution' / (case + '.json')))
        if kind == 'replay':
            e.pop('MIMALLOC_VERBOSE')
            e['LEAN_STACK_SIZE_KB'] = '65536'
        require(len(json.dumps(dict(argv=argv, env=e, stage=kind)).encode()) <= 4096, 'Accepted launcher configuration bound exceeded')
        p = dict(stage=kind, module=module, case=case, argv=argv, env=e, sources=list(map(str, submitted)),
                 cwd=str(work / 'audit' / case if kind == 'audit' else work))
        p['source_bindings'] = [bind(x) for x in p['sources']]
        result.append(p)
    return result

def execute_four(plans, child, finish):
    from finite_contract import CONTRACT
    require([(p['module'], p['stage']) for p in plans] == [(CONTRACT['modules'][0], s) for s in ['compile', 'resolve', 'replay', 'audit']], 'Bridge schedule differs')
    stages = []
    for p in plans:
        receipt = child(p)
        stages.append(dict(module=p['module'], stage=p['stage'], attempt_id=receipt['attempt_id']))
    return dict(stages=stages, result=finish())

def boundary_inputs(spec, roots, semantic, bind):
    from package_selection import selected_path
    from finite_contract import CONTRACT
    result = {}
    rows = spec['external_boundary_sources']
    require(rows == CONTRACT['external_boundary_sources'] and len(rows) == len({r['module'] for r in rows}) == 27, 'External source boundary differs')
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
        require(source.read_bytes() == raw, 'Boundary source differs from pinned package Git object')
        result[str(source)] = bind(source)
    return result

def finite_scope(spec):
    from finite_contract import CONTRACT
    require(len(CONTRACT['modules']) == 1, 'Bridge authority is not singleton')
    names = [r['module'] for r in spec['dependencies']]
    require(len(names) == len(set(names)) == 80 and set(names) == set(CONTRACT['imports'][CONTRACT['modules'][0]]), 'Exact80 bridge import set differs')
    origins = {r['module']: r['origin'] for r in spec['dependencies']}
    require(sorted(origins.values()) == sorted(['ordinary_build'] * 77 + ['paid'] * 2 + ['decoder']), 'Bridge origin split differs')
    require({m: origin for m, origin in origins.items() if origin != 'ordinary_build'} == CONTRACT['staged_origins'], 'Bridge staged module origins differ')
    expected_source_roots = list(dict.fromkeys(r['path'].split('/staged/',1)[0]+'/staged' for r in spec['dependencies'] if r['origin']!='ordinary_build'))
    require(spec['dependency_staged_roots'] == expected_source_roots, 'Bound staged source roots differ')
    require(len(spec['sources']) == 3 and {r['role'] for r in spec['sources']} == {'bridge','resolver','audit'}, 'Bridge submitted source roles differ')
    proof = next(row for row in spec['sources'] if row['role'] == 'bridge')
    require({k: proof[k] for k in ['path', 'bytes', 'sha256']} == CONTRACT['reviewed_source'], 'Reviewed bridge source fingerprint differs')
    require(spec['resource_contract'] == CONTRACT['resources'] and spec['execution_order'] == ['compile','resolve','replay','audit'], 'Accepted resource/schedule metadata differs')
    require(spec['pins'] == CONTRACT['pins'] and spec['tool_hashes'] == CONTRACT['tool_hashes'] and
            spec['toolchain'] == 'leanprover/lean4:v4.34.0' and spec['external_boundary_sources'] == CONTRACT['external_boundary_sources'], 'Accepted toolchain/package/boundary metadata differs')
    require(spec['project_imports'] == 80 and spec['project_modules_including_target'] == 81 and
            spec['required_theorem_roots'] == CONTRACT['required_roots'][CONTRACT['modules'][0]] and
            spec['required_interfaces'] == CONTRACT['interfaces'][CONTRACT['modules'][0]], 'Bridge declaration/import scope metadata differs')
    return set(names), origins

def verify_schedule(plans, evidence, lease, dependencies, handoff, identity, verify_receipts):
    from finite_contract import CONTRACT
    case = plans[0]['case']
    head = identity['GITHUB_SHA']
    verify_receipts(evidence / case, lease, plans, dependencies, head, expected_source=head)
    ids, previous = set(handoff['prior_attempt_ids']), handoff['last_release_ns']
    require(len(ids) == 13 and handoff['last_release_ns'] < lease['acquired_ns'], 'Producer identities/new lease boundary differs')
    for p in plans:
        r = load(evidence / case / p['stage'] / 'receipt.json')
        require(r.get('CI_identity') == identity and r.get('workflow_job') == 'check' and r.get('focused_module') == CONTRACT['modules'][0] and r.get('focused_case') == case, 'Bridge receipt identity differs')
        require(r['attempt_id'] not in ids and previous < r['started_ns'], 'Duplicate/overlapping bridge child')
        ids.add(r['attempt_id']); previous = r['ended_ns']
    require(len(ids) == 17 and lease['state'] == 'released' and lease.get('kernel_echild') and not lease.get('release_errors'), 'Bridge schedule/release incomplete')

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
    from bridge_context import FocusedContext
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
    roots = [work / 'objects', handoff['paid']['root'] / 'work/objects', handoff['decoder']['root'] / 'work/objects', *normal]
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
        paid_root=str(handoff['paid']['root']), decoder_root=str(handoff['decoder']['root']),
        producer_leases={k: handoff[k]['lease'] for k in ['paid', 'decoder']}, retained_context=matched,
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
                r = child_runner.run_child(p, Path(p['cwd']), evidence / p['case'] / p['stage'], context, accounting=accounting)
                path = evidence / p['case'] / p['stage'] / 'receipt.json'
                context.evidence_files[str(path)] = bind(path)
                return r
            state.update(execute_four(plans, child, context.finish))
        verify_schedule(plans, evidence, lease.record, dependencies, handoff, identity, verify_receipts)
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
    cache = temp / ('light-eft-paid-joint-bridge-python-' + suffix)
    require(sys.dont_write_bytecode and sys.pycache_prefix == str(cache) and not cache.exists(), 'Fresh absent -B Python cache prefix required')
    root = temp / ('light-eft-paid-joint-bridge-' + suffix)
    root.mkdir(mode=0o700, exist_ok=False)
    try:
        require(run_stage(root, env, bound_spec())['accepted'], 'Bridge focused gate failed')
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
