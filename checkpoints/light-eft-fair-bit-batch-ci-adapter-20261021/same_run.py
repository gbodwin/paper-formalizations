"""Authenticate completed paid/decoder producers; never launches a process."""
from contextlib import contextmanager
from pathlib import Path
import json, os, stat, sys, types
from contracts import bind, regular, require, SUFFIXES, tree
from ci_handoff import indexed_evidence, prior_bindings, retained_context, verify_decoder
from prior_guard import capture

PAID = 'checkpoints/light-eft-paid-focused-adapter-20261020'

def module_at(path, name):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(Path(path).read_bytes(), str(path), 'exec'), module.__dict__)
    return module

@contextmanager
def producer_contract(module):
    # Producer command/audit reconstruction is pure and happens before any child.
    # Restore even on failure; the active bridge authority is never expanded.
    sentinel = object()
    old = sys.modules.get('finite_contract', sentinel)
    sys.modules['finite_contract'] = module
    try:
        yield
    finally:
        if old is sentinel:
            sys.modules.pop('finite_contract', None)
        else:
            sys.modules['finite_contract'] = old

def document(root, protected, relative):
    path = Path(root) / relative
    require(str(path) in protected, 'Unindexed producer document: ' + relative)
    return json.loads(regular(path)[1])

def kernel_context():
    return dict(boot=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
                namespaces={n: os.readlink('/proc/self/ns/' + n) for n in ['pid', 'mnt', 'cgroup']})

def released_lease(root, lease):
    root = Path(root)
    current = kernel_context()
    require(lease.get('state') == 'released' and lease.get('kernel_echild') is True and not lease.get('release_errors'), 'Producer lease not cleanly released')
    require(lease.get('boot_id') == current['boot'] and lease.get('namespace') == current['namespaces'], 'Producer boot/namespace differs')
    require(lease.get('synthetic_fixture') is False and lease.get('historical_continuity') is False, 'Producer synthetic/historical lease')
    lock = root / 'ci-single-compiler.lock'
    require(lease.get('path') == str(lock), 'Wrong producer lock path')
    s, d = lock.lstat(), root.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1 and stat.S_IMODE(s.st_mode) == 0o600 and s.st_uid == os.getuid(), 'Unsafe producer lock')
    require([s.st_dev, s.st_ino] == [lease.get('device'), lease.get('inode')] and [d.st_dev, d.st_ino] == lease.get('directory_identity'), 'Producer lock/directory identity differs')
    require(type(lease.get('acquired_ns')) is int and type(lease.get('release_ns')) is int and lease['acquired_ns'] < lease['release_ns'], 'Producer lease timing invalid')

def rows_by_path(rows):
    require(isinstance(rows, list), 'Missing producer output ledger')
    result = {r['path']: r for r in rows}
    require(len(result) == len(rows), 'Duplicate producer output path')
    return result

def emitted_objects(root, modules, protected, final_rows):
    objects = Path(root) / 'work/objects'
    final = rows_by_path(final_rows)
    require(tree(objects) == final, 'Producer object tree/ledger differs')
    observed, result = {}, {}
    for module in modules:
        primary = objects / Path(*module.split('.')).with_suffix('.olean')
        stem = str(primary)[:-len('.olean')]
        parts = {p: r for p, r in final.items() if p.startswith(stem) and p[len(stem):] in SUFFIXES}
        require(str(primary) in parts, 'Missing producer primary')
        semantic = {p[len(stem):] for p in parts} & {'.olean', '.olean.private', '.olean.server'}
        require(semantic in [{'.olean'}, {'.olean', '.olean.private', '.olean.server'}], 'Incomplete producer semantic family')
        require(stem + '.ir.sig' not in parts or stem + '.ir' in parts, 'Producer IR signature missing IR')
        for p, row in parts.items():
            require(bind(p) == row == protected.get(p), 'Producer part/index identity differs')
        observed.update(parts)
        result[module] = dict(primary=dict(parts[str(primary)], module=module), parts=parts)
    require(observed == final, 'Foreign/prefix producer output')
    return result

def verify_paid(repo, tool, env, identity, normal_roots, verify_receipts, verify_singleton):
    repo = Path(repo)
    suffix = identity['GITHUB_RUN_ID'] + '-' + identity['GITHUB_RUN_ATTEMPT']
    root = Path(env['RUNNER_TEMP']) / ('light-eft-paid-focused-' + suffix)
    protected = indexed_evidence(root)
    doc = lambda name: document(root, protected, name)
    result, lease = doc('result.json'), doc('lease.json')
    require(result.get('accepted') is True and not result.get('failure'), 'Paid producer failed')
    require(result.get('CI_identity') == identity and doc('production-claim.json') == identity, 'Paid producer CI identity differs')
    require(result.get('source_commit') == result.get('harness_commit') == identity['GITHUB_SHA'], 'Paid producer source differs')
    require(result.get('dependency_qualification') == 'Fresh ordinary-CI build objects; no historical preservation or authenticated clean cache provenance', 'Paid producer qualification differs')
    released_lease(root, lease)
    spec = json.loads((repo / PAID / 'ci-spec.json').read_text())
    contract = module_at(repo / PAID / 'finite_contract.py', '_bound_paid_contract')
    policy = module_at(repo / PAID / 'ci_gate.py', '_bound_paid_policy')
    auditor = module_at(repo / PAID / 'audit_check.py', '_bound_paid_auditor')
    modules = contract.CONTRACT['modules']
    require(len(modules) == 2 and len(spec['dependencies']) == 16 and
            [len(contract.CONTRACT['imports'][m]) for m in modules] == [13, 17], 'Paid finite import contract differs')
    roots = [root / 'work/objects', *normal_roots]
    with producer_contract(contract):
        plans = policy.build_plans(tool, root / 'work', spec, roots, identity['GITHUB_SHA'], bind)
    require(doc('plans.json') == plans and len(plans) == 9, 'Paid recorded plan differs')
    objects = emitted_objects(root, modules, protected, result['result']['outputs']['new_objects'])
    ordinary = {r['module']: dict(bind(normal_roots[0] / Path(*r['module'].split('.')).with_suffix('.olean')), module=r['module']) for r in spec['dependencies']}
    all_deps = dict(ordinary, **{m: objects[m]['primary'] for m in modules})
    receipts, journals, audits = [], [], {}
    for index, module in enumerate(modules):
        case = module.rsplit('.', 1)[-1]
        part = plans[index * 4:index * 4 + 4]
        deps = {m: all_deps[m] for m in contract.CONTRACT['imports'][module]}
        verify_receipts(root / 'runtime' / case, lease, part, deps, identity['GITHUB_SHA'], expected_source=identity['GITHUB_SHA'])
        for p in part:
            receipts.append(doc('runtime/' + case + '/' + p['stage'] + '/receipt.json'))
        journals.append(prior_bindings((root / 'runtime' / case / 'inputs.jsonl').read_text()))
        raw = (root / 'runtime' / case / 'audit/raw.log').read_text()
        with producer_contract(contract):
            audits[module] = auditor.validate(root / 'work/audit' / case / 'ci-evidence', deps, raw, module)
    verify_singleton(root / 'runtime/PaidFlagFixtures', lease, plans[8:], all_deps, identity['GITHUB_SHA'], expected_source=identity['GITHUB_SHA'])
    receipts.append(doc('runtime/PaidFlagFixtures/compile/receipt.json'))
    journals.append(prior_bindings((root / 'runtime/PaidFlagFixtures/inputs.jsonl').read_text()))
    require(journals[0] == journals[1] == journals[2], 'Paid producer journals differ')
    require(result['result']['audits'] == audits, 'Paid recorded audit result differs')
    previous, ids, expected = 0, set(), []
    for i, (p, receipt) in enumerate(zip(plans, receipts, strict=True)):
        require(receipt.get('CI_identity') == identity and receipt.get('synthetic_fixture') is False and
                receipt.get('dependency_qualification') == 'NEWLY_OBSERVED_ORDINARY_CI_DEPENDENCIES; no historical object/provenance continuity', 'Paid child identity/qualification differs')
        require(receipt.get('focused_module') == p['module'] and receipt.get('focused_case') == p['case'], 'Paid child finite authority differs')
        require(receipt['attempt_id'] not in ids and previous < receipt['started_ns'] < receipt['ended_ns'], 'Paid duplicate/overlapping child')
        ids.add(receipt['attempt_id']); previous = receipt['ended_ns']
        wanted = {path: row for m in modules[:(1 if i < 4 else 2)] for path, row in objects[m]['parts'].items()}
        require(rows_by_path(receipt['outputs_after']['new_objects']) == wanted, 'Paid growing output union differs')
        expected.append(dict(module=p['module'], stage=p['stage'], attempt_id=receipt['attempt_id']))
    require(result.get('stages') == expected and lease['acquired_ns'] <= receipts[0]['started_ns'] and previous <= lease['release_ns'], 'Paid stage/lease schedule differs')
    return dict(root=root, protected=protected, lease=lease, stages=expected, receipts=receipts,
                objects=objects, prior_bindings=journals[0], retained_roots=list(map(str, normal_roots)))

def collect(repo, tool, env, identity, spec, normal_roots, verify_receipts, verify_singleton):
    paid = verify_paid(repo, tool, env, identity, normal_roots, verify_receipts, verify_singleton)
    decoder = verify_decoder(repo, tool, env, identity, spec, verify_receipts)
    released_lease(decoder['root'], decoder['lease'])
    require(paid['lease']['release_ns'] < decoder['lease']['acquired_ns'], 'Paid/decoder leases overlap or reorder')
    decoder_receipts = [document(decoder['root'], decoder['protected'], 'runtime/' + s['stage'] + '/receipt.json') for s in decoder['stages']]
    ids = [r['attempt_id'] for r in paid['receipts'] + decoder_receipts]
    require(len(ids) == len(set(ids)) == 13 and paid['receipts'][-1]['ended_ns'] < decoder_receipts[0]['started_ns'], 'Producer children duplicate/overlap')
    staged = {m: v['primary'] for m, v in paid['objects'].items()}
    m = decoder['item']['module']
    staged[m] = dict(bind(decoder['paths']['.olean']), module=m)
    protected = {**paid['protected'], **decoder['protected']}
    return dict(paid=paid, decoder=decoder, protected=protected, staged=staged,
                trees=capture([paid['root'], decoder['root']]), prior_attempt_ids=ids,
                last_release_ns=decoder['lease']['release_ns'])

def retained(handoff, normal_roots, classified, inputs):
    return {name: retained_context(handoff[name], normal_roots, classified['semantic'], inputs)
            for name in ['paid', 'decoder']}

# Preserve the accepted producer reconstruction above. Extend only the finite
# handoff by authenticating its already completed bridge consumer as producer.
_collect_paid_decoder = collect
BRIDGE = 'checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020'

def verify_bridge(repo, tool, env, identity, normal_roots, earlier, verify_receipts):
    repo=Path(repo)
    suffix=identity['GITHUB_RUN_ID']+'-'+identity['GITHUB_RUN_ATTEMPT']
    root=Path(env['RUNNER_TEMP'])/('light-eft-paid-joint-bridge-'+suffix)
    protected=indexed_evidence(root)
    doc=lambda name:document(root,protected,name)
    result,lease=doc('result.json'),doc('lease.json')
    spec=json.loads((repo/BRIDGE/'ci-spec.json').read_text())
    contract=module_at(repo/BRIDGE/'finite_contract.py','_bound_bridge_contract')
    policy=module_at(repo/BRIDGE/'ci_gate.py','_bound_bridge_policy')
    auditor=module_at(repo/BRIDGE/'audit_check.py','_bound_bridge_auditor')
    require(result.get('accepted') is True and not result.get('failure'),'Bridge producer failed')
    require(result.get('CI_identity')==identity and result.get('workflow_job')=='check' and
            doc('production-claim.json')==identity,'Bridge producer CI/job identity differs')
    require(result.get('source_commit')==result.get('harness_commit')==identity['GITHUB_SHA'],
            'Bridge producer source/harness differs')
    require(result.get('dependency_qualification')==spec['dependency_qualification'],
            'Bridge producer provenance qualification differs')
    released_lease(root,lease)
    module=contract.CONTRACT['modules'][0]
    require(len(contract.CONTRACT['modules'])==1 and len(spec['dependencies'])==80,
            'Accepted bridge finite scope differs')
    retained_roots=[earlier['paid']['root']/'work/objects',earlier['decoder']['root']/'work/objects',*normal_roots]
    roots=[root/'work/objects',*retained_roots]
    dependencies={r['module']:earlier['staged'][r['module']] if r['module'] in earlier['staged'] else
        dict(bind(normal_roots[0]/Path(*r['module'].split('.')).with_suffix('.olean')),module=r['module'])
        for r in spec['dependencies']}
    with producer_contract(contract):
        policy.finite_scope(spec)
        plans=policy.build_plans(tool,root/'work',spec,roots,identity['GITHUB_SHA'],bind)
        require(doc('plans.json')==plans,'Bridge recorded plan differs')
        policy.verify_schedule(plans,root/'runtime',lease,dependencies,earlier,identity,verify_receipts)
    case=module.rsplit('.',1)[-1]
    receipts=[doc('runtime/'+case+'/'+p['stage']+'/receipt.json') for p in plans]
    objects=emitted_objects(root,[module],protected,result['result']['outputs']['new_objects'])
    expected=[]
    for p,receipt in zip(plans,receipts,strict=True):
        require(receipt.get('synthetic_fixture') is False and
                receipt.get('dependency_qualification')=='NEWLY_OBSERVED_ORDINARY_CI_DEPENDENCIES; no historical object/provenance continuity',
                'Bridge child provenance differs')
        require(rows_by_path(receipt['outputs_after']['new_objects'])==objects[module]['parts'],
                'Bridge growing output union differs')
        expected.append(dict(module=module,stage=p['stage'],attempt_id=receipt['attempt_id']))
    require(result['stages']==expected,'Bridge recorded stage order differs')
    with producer_contract(contract):
        audit=auditor.validate(root/'work/audit'/case/'ci-evidence',dependencies,
            (root/'runtime'/case/'audit/raw.log').read_text(),module)
    require(result['result']['audits']=={module:audit} and result['result']['preserved'] is True,
            'Bridge recorded audit/preservation differs')
    previous=doc('same-run-handoff.json')
    require(previous['CI_identity']==identity and previous['workflow_job']=='check' and
            previous['prior_attempt_ids']==earlier['prior_attempt_ids'] and
            previous['paid_root']==str(earlier['paid']['root']) and previous['decoder_root']==str(earlier['decoder']['root']) and
            previous['producer_leases']=={k:earlier[k]['lease'] for k in ['paid','decoder']} and
            previous['staged_objects']==earlier['staged'], 'Bridge original handoff differs')
    journal=prior_bindings((root/'runtime'/case/'inputs.jsonl').read_text())
    return dict(root=root,protected=protected,lease=lease,receipts=receipts,stages=expected,
                objects=objects,prior_bindings=journal,retained_roots=list(map(str,retained_roots)))

def collect(repo,tool,env,identity,spec,normal_roots,verify_receipts,verify_singleton):
    bridge_spec=json.loads((Path(repo)/BRIDGE/'ci-spec.json').read_text())
    earlier=_collect_paid_decoder(repo,tool,env,identity,bridge_spec,normal_roots,verify_receipts,verify_singleton)
    bridge=verify_bridge(repo,tool,env,identity,normal_roots,earlier,verify_receipts)
    require(earlier['last_release_ns']<bridge['lease']['acquired_ns'],'Decoder/bridge leases overlap')
    ids=earlier['prior_attempt_ids']+[r['attempt_id'] for r in bridge['receipts']]
    require(len(ids)==len(set(ids))==17 and earlier['last_release_ns']<bridge['receipts'][0]['started_ns'],
            'Duplicate or overlapping three-producer children')
    staged={**earlier['staged'],**{m:v['primary'] for m,v in bridge['objects'].items()}}
    return dict(paid=earlier['paid'],decoder=earlier['decoder'],bridge=bridge,
        staged=staged,protected={**earlier['protected'],**bridge['protected']},
        trees=capture([earlier['paid']['root'],earlier['decoder']['root'],bridge['root']]),
        prior_attempt_ids=ids,last_release_ns=bridge['lease']['release_ns'])

def retained(handoff,normal_roots,classified,inputs):
    return {name:retained_context(handoff[name],
                [handoff['paid']['root']/'work/objects',handoff['decoder']['root']/'work/objects',*normal_roots]
                if name=='bridge' else normal_roots,classified['semantic'],inputs)
            for name in ['paid','decoder','bridge']}
