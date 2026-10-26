"""Explicit actual-job qualification only; no full/focused/replay authority.

Data preparation is outside the later native-child boundary. The real caller
must retain its original admission/resource/lease/preservation/cleanup checks.
No historical artifact or cache receipt can supply the producer observation.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import stat
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORKFLOW = '.github/workflows/light-eft-probe-main-qualification.yml'
PURPOSE = 'reacquisition_qualification'
QUALIFICATION = 'GENUINE_NATIVE_REACQUISITION_QUALIFICATION_ONLY_V1'
ATTESTATION = 'qualification-attestation.json'
JOBS = {'producer': 'native_probe_main', 'consumer': 'native_reacquisition_consumer'}
IDENTITY = ('GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_REF', 'GITHUB_RUN_ID',
            'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB', 'GITHUB_WORKFLOW', 'GITHUB_WORKFLOW_SHA',
            'GITHUB_WORKFLOW_REF', 'LEAN_NUM_THREADS', 'LIGHTEFT_JOB_WORKFLOW_REPOSITORY',
            'LIGHTEFT_JOB_WORKFLOW_PATH', 'LIGHTEFT_JOB_WORKFLOW_SHA',
            'LIGHTEFT_JOB_WORKFLOW_REF', 'LIGHTEFT_REACQUISITION_ROLE')


def identity(cl):
    e = os.environ; role = e.get('LIGHTEFT_REACQUISITION_ROLE')
    cl.require(role in JOBS and e.get('GITHUB_JOB') == JOBS[role] and
               e.get('LIGHTEFT_HANDOFF_PURPOSE') == PURPOSE and
               e.get('GITHUB_ACTIONS') == 'true' and
               e.get('GITHUB_REPOSITORY') == 'gbodwin/paper-formalizations' and
               e.get('GITHUB_REF') == 'refs/heads/light-eft-spanners-checkpoints' and
               e.get('GITHUB_EVENT_NAME') == 'push' and e.get('LEAN_NUM_THREADS') == '1',
               'Wrong genuine qualification purpose/job')
    head = cl.git('rev-parse', 'HEAD').decode().strip()
    repo = e['GITHUB_REPOSITORY']; ref = e['GITHUB_REF']
    cl.require(e.get('GITHUB_SHA') == e.get('GITHUB_WORKFLOW_SHA') == head and
               e.get('GITHUB_WORKFLOW') == 'LightEFT probe main profile qualification' and
               e.get('GITHUB_WORKFLOW_REF') == repo + '/' + WORKFLOW + '@' + ref and
               e.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY') == repo and
               e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == WORKFLOW and
               e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == head and
               e.get('LIGHTEFT_JOB_WORKFLOW_REF') in
               [repo + '/' + WORKFLOW + '@' + ref, repo + '/' + WORKFLOW + '@' + head] and
               all(e.get(k, '').isdecimal() and int(e[k]) > 0 for k in
                   ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Qualification workflow/source differs')
    return {k: e[k] for k in IDENTITY}


def sdk_home(ci):
    return ROOT / '.lake' / ('light-eft-qualification-sdk-' + ci['GITHUB_RUN_ID'] + '-' + ci['GITHUB_RUN_ATTEMPT'])


def producer_identity(ci):
    # Expected record of the OTHER genuine job; never an executing environment.
    return dict(ci, GITHUB_JOB=JOBS['producer'], LIGHTEFT_REACQUISITION_ROLE='producer')


def clean_lifecycle(cl, receipt, lease):
    cl.require(receipt['state'] == 'finished' and receipt['exit'] == 0 and
               receipt.get('synthetic_fixture') is False and
               all(receipt.get(k) is True for k in ['kernel_limits_verified', 'direct_reaped',
                   'waitid_wait4_status_match', 'kernel_no_children_verified', 'all_descendants_gone']) and
               not receipt.get('failure') and not receipt.get('cleanup_errors') and
               lease['state'] == 'released' and lease.get('kernel_echild') is True and
               lease.get('synthetic_fixture') is False and
               not lease.get('release_errors'), 'Incomplete genuine qualification lifecycle')


def seal_observed(cl, graph, names, tool, tools, roots, kinds, bound, ci, root, receipt, inputs, observed):
    cl.require(identity(cl) == ci and ci['LIGHTEFT_REACQUISITION_ROLE'] == 'producer' and
               receipt['exit'] == 0 and receipt.get('direct_reaped') is True and
               receipt.get('synthetic_fixture') is False, 'No actual native producer observation')
    nodes, _ = cl.validate_graph(graph, names)
    objects, sources, claims, paths = observed
    before = cl.snapshot(paths)
    for path in paths:
        p = str(path); value = before[p]
        cl.require(p in inputs and all(inputs[p][k] == value[k] for k in ['bytes', 'sha256']),
                   'Observed qualification object was not protected before native exec')
    cl.write_snapshot(root / 'qualification-producer-before', before)
    bundle = root / 'bundle'; bundle.mkdir(mode=0o700, exist_ok=False)
    (bundle / 'parts').mkdir(mode=0o700)
    _, seeds, imported, _ = cl.selection(graph, names)
    files = []; payload = 0
    for name, node in sorted(nodes.items()):
        obj = objects[name]; index = obj['root']; base = roots[index] / obj['relative']
        for suffix in cl.required_suffixes(name, node, obj['available'], seeds, imported):
            path = cl.part_path(base, suffix); value = obj['available'][suffix]
            row = dict(module=name, suffix=suffix, root=index,
                       relative=path.relative_to(roots[index]).as_posix(),
                       acquisition=cl.acquisition(kinds[index]), transfer=kinds[index] == 'project',
                       chunks=[], **value)
            if row['transfer']:
                cl.require(payload + row['bytes'] <= cl.PAYLOAD_LIMIT, 'Project qualification payload ceiling')
                row['chunks'] = cl.copy_parts(path, bundle, len(files), before[str(path)])
                payload += row['bytes']
            files.append(row)
    manifest = dict(schema='LIGHT_SAME_RUN_REPLAY_HANDOFF_V3', producer=ci, controls=bound,
                    acquisition_policy=cl.ACQUISITION_POLICY, tools=tools, packages=cl.PINS,
                    root_kinds=kinds, graph=graph, sources=sources, objects=objects,
                    prefix_claims=claims, files=files, payload_bytes=payload, qualification=QUALIFICATION,
                    snapshot=dict(observed_inputs_unchanged=True, external_no_writer_required=True,
                                  hostile_writer_absence_not_proved=True),
                    captures=[dict(schema='QUALIFICATION_ACTUAL_NATIVE_OBSERVATION_V1',
                                   identity=ci, attempt=receipt['attempt_id'],
                                   child=receipt['child_identity'], synthetic_fixture=False)])
    result = cl.seal_manifest(bundle, manifest)
    cl.require(cl.snapshot(paths) == before and cl.prefixes(roots) == claims and
               identity(cl) == ci and cl.controls() == bound and
               cl.runtime()[1:] == (tools, roots, kinds), 'Producer observed input correlation changed')
    cl.write_snapshot(root / 'qualification-producer-after', cl.snapshot(paths))
    return dict(qualification_only=True, production_acceptance=False, bundle=str(bundle),
                observed_project_payload_bytes=payload, **result)


def finish_producer(cl, ci, root, receipt, lease, outputs):
    cl.require(identity(cl) == ci and ci['LIGHTEFT_REACQUISITION_ROLE'] == 'producer',
               'Wrong actual attestation producer')
    clean_lifecycle(cl, receipt, lease)
    row = dict(schema='GENUINE_NATIVE_REACQUISITION_ATTESTATION_V1', purpose=PURPOSE,
               producer=ci, manifest_sha256=outputs['manifest_sha256'], attempt=receipt['attempt_id'],
               runtime_receipt=cl.digest(root / 'runtime/receipt.json'), lease_receipt=cl.digest(root / 'lease.json'),
               exit=receipt['exit'], synthetic_fixture=False,
               facts={k: receipt[k] for k in ['kernel_limits_verified', 'direct_reaped',
                    'waitid_wait4_status_match', 'kernel_no_children_verified', 'all_descendants_gone']},
               lease_state=lease['state'], lease_kernel_echild=lease['kernel_echild'],
               lease_synthetic_fixture=lease['synthetic_fixture'],
               no_cleanup_or_release_errors=True, production_acceptance=False)
    raw = cl.encoded(row)
    cl.create(root / 'qualification-attestation-attempt.json', cl.encoded(dict(
        attempted_bytes=len(raw), attempted_sha256=hashlib.sha256(raw).hexdigest(),
        total_transfer_bytes_if_written=outputs['total_transfer_bytes'] + len(raw),
        total_cap=cl.PAYLOAD_LIMIT, attestation_cap=16384, acceptance=False)))
    cl.require(len(raw) <= 16384 and
               outputs['total_transfer_bytes'] + len(raw) <= cl.PAYLOAD_LIMIT,
               'Attestation or complete project/metadata/attestation transfer ceiling')
    cl.create(Path(outputs['bundle']) / ATTESTATION, raw)
    result = dict(handoff_manifest_sha256=outputs['manifest_sha256'],
                  handoff_attestation_sha256=hashlib.sha256(raw).hexdigest(),
                  handoff_producer_sha=ci['GITHUB_SHA'], handoff_producer_run_id=ci['GITHUB_RUN_ID'],
                  handoff_producer_run_attempt=ci['GITHUB_RUN_ATTEMPT'])
    # Only after truthful native and real lease cleanup; upload also requires success.
    with open(os.environ['GITHUB_OUTPUT'], 'a') as stream:
        for key, value in result.items():stream.write(key + '=' + value + '\n')
    return result


def prepare_consumer(cl, ci, root, tool, tools, roots, kinds, names, bound):
    cl.require(identity(cl) == ci and ci['LIGHTEFT_REACQUISITION_ROLE'] == 'consumer',
               'Wrong actual qualification consumer')
    bundle, transport_path, transport_state, transport_row = cl.transport(ci, bound, purpose=PURPOSE)
    expected_producer = producer_identity(ci)
    attestation = bundle / ATTESTATION; cl.no_symlink_parents(attestation)
    observed_attestation = cl.observation(attestation)
    cl.require(attestation.lstat().st_nlink == 1, 'Aliased qualification attestation')
    cl.require(observed_attestation['bytes'] <= 16384 and observed_attestation['sha256'] ==
               os.environ['LIGHTEFT_QUALIFICATION_ATTESTATION_SHA256'], 'Producer attestation bytes differ')
    row = cl.read_json(attestation)
    cl.require(set(row) == {'schema', 'purpose', 'producer', 'manifest_sha256', 'attempt',
               'runtime_receipt', 'lease_receipt', 'exit', 'synthetic_fixture', 'facts',
               'lease_state', 'lease_kernel_echild', 'lease_synthetic_fixture',
               'no_cleanup_or_release_errors', 'production_acceptance'} and
               re.fullmatch('[0-9a-f]{32}', row['attempt']) and
               row['schema'] == 'GENUINE_NATIVE_REACQUISITION_ATTESTATION_V1' and
               row['purpose'] == PURPOSE and row['producer'] == expected_producer and
               row['manifest_sha256'] == os.environ['LIGHTEFT_HANDOFF_MANIFEST_SHA256'] and
               row['exit'] == 0 and row['synthetic_fixture'] is False and
               set(row['facts']) == {'kernel_limits_verified', 'direct_reaped',
                   'waitid_wait4_status_match', 'kernel_no_children_verified', 'all_descendants_gone'} and
               all(row['facts'].get(k) is True for k in ['kernel_limits_verified', 'direct_reaped',
                   'waitid_wait4_status_match', 'kernel_no_children_verified', 'all_descendants_gone']) and
               row['lease_state'] == 'released' and row['lease_kernel_echild'] is True and
               row['lease_synthetic_fixture'] is False and
               row['no_cleanup_or_release_errors'] is True and row['production_acceptance'] is False,
               'Producer attestation is not genuine cleaned-up qualification')
    cl.binding(row['runtime_receipt']); cl.binding(row['lease_receipt'])
    manifest, metadata_paths, metadata_bytes = cl.load_manifest(bundle, os.environ['LIGHTEFT_HANDOFF_MANIFEST_SHA256'])
    cl.require(set(manifest) == {'schema', 'producer', 'controls', 'tools', 'packages', 'root_kinds',
               'graph', 'sources', 'objects', 'prefix_claims', 'files', 'payload_bytes',
               'qualification', 'snapshot', 'captures', 'acquisition_policy'} and
               manifest['producer'] == expected_producer and manifest['controls'] == bound and
               manifest['schema'] == 'LIGHT_SAME_RUN_REPLAY_HANDOFF_V3' and
               manifest['qualification'] == QUALIFICATION and manifest['tools'] == tools and
               manifest['packages'] == cl.PINS and manifest['root_kinds'] == kinds and
               manifest['acquisition_policy'] == cl.ACQUISITION_POLICY,
               'Actual nonproduction qualification handoff differs')
    cl.require(manifest['captures'] and len(manifest['captures']) == 1 and
               manifest['captures'][0]['schema'] == 'QUALIFICATION_ACTUAL_NATIVE_OBSERVATION_V1' and
               manifest['captures'][0]['identity'] == expected_producer and
               manifest['captures'][0]['attempt'] == row['attempt'] and
               manifest['snapshot'] == dict(observed_inputs_unchanged=True,
                   external_no_writer_required=True, hostile_writer_absence_not_proved=True),
               'Qualification capture/attempt/snapshot differs')
    graph = manifest['graph']; nodes, _ = cl.validate_graph(graph, names)
    expected = cl.expected_file_set(manifest, nodes, names, kinds)
    attestation_bytes = observed_attestation['bytes']
    by_key, part_paths = cl.verify_files(bundle, manifest, expected, metadata_paths,
        metadata_bytes + attestation_bytes, extra_entries=(ATTESTATION,))
    sources = cl.verify_sources(manifest, nodes, tool)
    namespace = cl.package_namespace(roots, kinds)
    cl.require(all(x['prefixes'] == manifest['prefix_claims'][x['root']] for x in namespace),
               'Qualification package namespace differs')
    packages = cl.reacquired_package_paths(manifest, nodes, roots, kinds)
    stable = part_paths + sources + packages + [transport_path, attestation]
    stable += [tool / 'bin' / n for n in ['lean', 'leanchecker', 'lake']]
    stable += [sdk_home(ci) / rel for rel in transport_row['loaded_code']]
    destinations = set()
    for value in by_key.values():
        dest = roots[value['root']] / cl.safe_relative(value['relative']); cl.no_symlink_parents(dest)
        cl.require(dest not in destinations, 'Aliased/duplicate qualification destination')
        destinations.add(dest)
        if value['transfer']:
            cl.require(not os.path.lexists(dest), 'Existing project qualification object')
        else:
            cl.require(cl.digest(dest) == {k: value[k] for k in ['bytes', 'sha256']},
                       'Qualification dependency differs from exact producer bytes')
            stable.append(dest)
    before = cl.snapshot(stable); cl.write_snapshot(root / 'consumer-inputs-before', before)
    progress = []
    try:
        cl.restore_project_rows(bundle, list(by_key.values()), roots, before, progress, root)
    finally:
        cl.create(root / 'project-restore-progress.json', cl.encoded(progress))
    cl.require(cl.snapshot(stable) == before and cl.package_namespace(roots, kinds) == namespace and
               cl.observation(transport_path) == transport_state and
               cl.observation(attestation) == observed_attestation, 'Qualification preparation changed inputs')
    restored = [roots[x['root']] / cl.safe_relative(x['relative']) for x in by_key.values() if x['transfer']]
    state = dict(manifest=manifest, protected_paths=sorted(set(stable + restored), key=str),
                 snapshot=cl.snapshot(stable + restored), package_namespace=namespace,
                 transfer_bytes=manifest['payload_bytes'] + metadata_bytes + attestation_bytes,
                 producer_attestation_sha256=observed_attestation['sha256'])
    cl.write_snapshot(root / 'consumer-prepared-inputs', state['snapshot'])
    return state


def verify_consumer(cl, ci, graph, names, tool, tools, roots, kinds, bound, state):
    cl.require(identity(cl) == ci and ci['LIGHTEFT_REACQUISITION_ROLE'] == 'consumer',
               'Wrong actual metadata consumer')
    manifest = state['manifest']; nodes, _ = cl.validate_graph(manifest['graph'], names)
    cl.verify_restored_graph(graph, manifest['graph'], names, nodes, manifest['sources'],
                            manifest['objects'], roots, tool)
    available, _ = cl.actual_companions(set(nodes), manifest['objects'], roots)
    _, seeds, imported, _ = cl.selection(manifest['graph'], names)
    for name in nodes:
        cl.require(cl.required_suffixes(name, nodes[name], available[name], seeds, imported) ==
                   cl.required_suffixes(name, nodes[name], manifest['objects'][name]['available'], seeds, imported),
                   'Actual qualification companion read set differs')
    cl.require(cl.package_census(graph, kinds) == cl.package_census(manifest['graph'], kinds) and
               cl.package_namespace(roots, kinds) == state['package_namespace'] and
               cl.snapshot(state['protected_paths']) == state['snapshot'] and
               cl.controls() == bound and cl.runtime()[1:] == (tools, roots, kinds),
               'Actual native dependency/namespace/input preservation differs')
    cl.reacquired_package_paths(manifest, nodes, roots, kinds)
    return dict(nonproduction_reacquisition_metadata_comparison_passed=True,
                production_acceptance=False, checker_invocations=0, target_count=567,
                total_transfer_bytes=state['transfer_bytes'],
                producer_attestation_sha256=state['producer_attestation_sha256'])


def main():
    if not(sys.flags.isolated and sys.dont_write_bytecode):raise ValueError('Use -I -B')
    path = HERE / 'closure_contract.py'; raw = path.read_bytes()
    import subprocess
    exact = subprocess.run(['git', 'show', 'HEAD:' + path.relative_to(ROOT).as_posix()],
                           cwd=ROOT, capture_output=True, check=True, timeout=10).stdout
    if raw != exact or any(p.is_symlink() for p in [path, *path.parents]):raise ValueError('Changed contract')
    spec = importlib.util.spec_from_file_location('_qualification_data_contract', path)
    cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
    cl.controls(); ci = identity(cl)
    cl.require(sys.argv[1:] == ['sdk-prepare'] and ci['LIGHTEFT_REACQUISITION_ROLE'] == 'consumer',
               'Only fixed qualification SDK preparation')
    dest = sdk_home(ci); cl.no_symlink_parents(dest); dest.mkdir(mode=0o700, exist_ok=False)
    for name in ['package.json', 'package-lock.json']:
        path = HERE / name; raw = path.read_bytes()
        cl.require(raw == cl.git('show', 'HEAD:' + path.relative_to(ROOT).as_posix()), 'SDK lock source differs')
        cl.create(dest / name, raw)
    cl.create(dest / 'sdk-preparation.json', cl.encoded(dict(identity=ci,
        source_package=cl.digest(HERE / 'package.json'), source_lock=cl.digest(HERE / 'package-lock.json'),
        destination=str(dest), install_not_yet_invoked=True, scripts_must_be_disabled=True,
        no_cache_or_build_provenance=True)))
    print(json.dumps(dict(purpose=PURPOSE, sdk_directory=str(dest), scripts_must_be_disabled=True)))


if __name__ == '__main__':main()
