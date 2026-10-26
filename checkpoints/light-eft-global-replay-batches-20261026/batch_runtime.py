"""SOURCE ONLY: fresh original launcher boundary and serial native batch.

Not child CILease/resource supervision: the original global replay had launcher
admission only. Native metadata profile, SDK and footprint remain unqualified.
All entrypoints refuse until the exact new controls are bound in all five specs.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import shutil
import signal
import stat
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INNER = '''/usr/bin/python3 -I -B checkpoints/light-eft-global-replay-batches-20261026/batch_runtime.py verify "$-" "$BASH_VERSION"
exec /usr/bin/python3 -I -B checkpoints/light-eft-global-replay-batches-20261026/batch_runtime.py run
'''
LEGACY = ROOT / 'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py'
LEGACY_SHA = '2bcbe3ba3a4154d61ff01a19b0dfc615a6b50f64b3eb09020765a299af7fe4be'


def load(path, name):
    raw = path.read_bytes()
    exact = subprocess.run(['git', 'show', 'HEAD:' + path.relative_to(ROOT).as_posix()],
                           cwd=ROOT, check=True, capture_output=True, timeout=10).stdout
    if raw != exact or any(p.is_symlink() for p in [path, *path.parents]):
        raise ValueError('Imported control differs from actual Git source')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def dependencies():
    route = load(HERE / 'route_status.py', '_bound_batch_route')
    role = os.environ.get('LIGHTEFT_VALIDATION_ROLE', '')
    route.require(role in ['full', 'global_replay'], 'Wrong finite launcher role')
    bound = route.controls(); ci = route.identity(role)
    route.require(hashlib.sha256(LEGACY.read_bytes()).hexdigest() == LEGACY_SHA,
                  'Original launcher observation primitives changed')
    old = load(LEGACY, '_bound_original_launcher_primitives')
    return route, route.contract(), old, bound, ci


def folder(ci):
    parent = Path(os.environ['RUNNER_TEMP'])
    if not parent.is_absolute() or parent.is_symlink() or not parent.is_dir():
        raise ValueError('Unsafe runner temporary root')
    slot = os.environ.get('LIGHTEFT_REPLAY_BATCH', 'producer')
    return parent / ('light-eft-batch-admission-' + ci['run_id'] + '-' + ci['run_attempt'] + '-' + slot)


def context(route, ci, bound):
    require = route.require
    require(Path.cwd().resolve() == ROOT, 'Wrong repository working directory')
    if ci['role'] == 'full':
        require('LIGHTEFT_REPLAY_BATCH' not in os.environ, 'Producer cannot select a replay batch')
        return dict(CI_identity=ci, controls=bound, batch='producer',
                    boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
                    namespaces={n: os.readlink('/proc/self/ns/' + n) for n in ['pid', 'mnt', 'cgroup']})
    number = os.environ.get('LIGHTEFT_REPLAY_BATCH')
    require(number in ['1', '2', '3'], 'Wrong finite batch')
    binding = route.handoff(ci); prior = route.previous(ci, int(number), binding)
    return dict(CI_identity=ci, controls=bound, batch=int(number), handoff=binding,
                previous_coverage_sha256=prior,
                boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
                namespaces={n: os.readlink('/proc/self/ns/' + n) for n in ['pid', 'mnt', 'cgroup']})


def platform(old):
    env = dict(os.environ)
    ids = dict(uid=os.getuid(), euid=os.geteuid(), gid=os.getgid(), egid=os.getegid())
    old.normal(env, ids)
    # checked_sources retains the original script/helper pins and five-spec
    # source rows; new route.controls independently covers the new caller paths.
    return dict(ids=ids, bash=old.binding('/bin/bash'), python=old.binding('/usr/bin/python3'),
                original_sources=old.checked_sources())


def fresh(route, old, ci, bound):
    home = folder(ci); boot, binding = old.load(home, 'bootstrap.json')
    route.require(boot['context'] == context(route, ci, bound) and boot['platform'] == platform(old),
                  'Fresh bootstrap source/platform/identity changed')
    return home, boot, binding


def bootstrap(route, old, ci, bound):
    home = folder(ci); home.mkdir(mode=0o700, exist_ok=False)
    selected = shutil.which('lake', path=os.environ.get('PATH', ''))
    route.require(selected is not None, 'No installed Lake/elan carrier')
    old.write(home, 'bootstrap.json', dict(context=context(route, ci, bound), platform=platform(old),
              observed_ns=time.monotonic_ns(), inherited_environment=old.projection(dict(os.environ)),
              lake_launcher=old.binding(selected),
              qualification='FRESH_BATCH_LAUNCHER_ADMISSION_ONLY; not resource/CILease or kernel acceptance'))


def before_lake(route, old, ci, bound):
    home, boot, boot_row = fresh(route, old, ci, bound)
    env = dict(os.environ); selected = shutil.which('lake', path=env.get('PATH', ''))
    route.require(old.projection(env) == boot['inherited_environment'] and selected and
                  old.binding(selected) == boot['lake_launcher'], 'Inherited environment/Lake carrier changed')
    old.write(home, 'before-lake.json', dict(context=boot['context'], bootstrap=boot_row,
              inherited_environment=old.projection(env), lake_launcher=boot['lake_launcher'],
              observed_ns=time.monotonic_ns()))
    signal.setitimer(signal.ITIMER_REAL, 0)
    os.execv(selected, [selected, 'env', '/usr/bin/python3', '-I', '-B', str(HERE / 'batch_runtime.py'), 'enter'])


def enter(route, old, ci, bound):
    home, boot, boot_row = fresh(route, old, ci, bound)
    before, before_row = old.load(home, 'before-lake.json')
    route.require(before['context'] == boot['context'] and before['bootstrap'] == boot_row and
                  before['lake_launcher'] == boot['lake_launcher'] and
                  before['inherited_environment'] == boot['inherited_environment'], 'Before-Lake binding differs')
    observed = old.observe_lake(dict(os.environ))
    old.write(home, 'lake-baseline.json', dict(context=boot['context'], bootstrap=boot_row,
              before_lake=before_row, baseline=observed, observed_ns=time.monotonic_ns()))
    signal.setitimer(signal.ITIMER_REAL, 0)
    os.execv('/bin/bash', ['/bin/bash', '--noprofile', '--norc', '-p', '-euo', 'pipefail', '-c', INNER])


def verified(route, old, ci, bound):
    home, boot, boot_row = fresh(route, old, ci, bound)
    saved, baseline_row = old.load(home, 'lake-baseline.json')
    before, before_row = old.load(home, 'before-lake.json')
    route.require(saved['context'] == boot['context'] and saved['bootstrap'] == boot_row and
                  saved['before_lake'] == before_row and before['context'] == boot['context'],
                  'Lake baseline/source binding differs')
    observed = old.observe_lake(dict(os.environ))
    old.equivalent(saved['baseline'], observed)
    return home, boot, boot_row, saved, baseline_row, observed


def verify(route, old, ci, bound, flags, version):
    route.require('p' in flags and version.startswith(('4.', '5.')), 'Unsupported inner Bash state/version')
    home, boot, boot_row, saved, baseline_row, observed = verified(route, old, ci, bound)
    old.write(home, 'verified.json', dict(context=boot['context'], bootstrap=boot_row,
              baseline=baseline_row, observed=observed, bash_flags=flags, bash_version=version,
              verified_ns=time.monotonic_ns(),
              qualification='Original launcher identity/environment equivalence only; replay still mandatory'))


def read_snapshot(route, cl, directory):
    index = route.read(directory / 'index.json'); values = {}; whole = hashlib.sha256()
    route.require(index['count'] <= 200000 and len(index['chunks']) <= 3125, 'Oversized snapshot index')
    for i, part in enumerate(index['chunks']):
        name = 'chunk-%05d.json' % i
        route.require(part['path'] == name and cl.digest(directory / name) ==
                      {k: part[k] for k in ['bytes', 'sha256']}, 'Snapshot chunk binding differs')
        rows = route.read(directory / name)
        route.require(len(rows) == part['count'] <= 64, 'Snapshot chunk count differs')
        for path, value in rows:
            route.require(path not in values and Path(path).is_absolute(), 'Duplicate/relative snapshot path')
            values[path] = value; whole.update(cl.encoded([path, value]))
    route.require(len(values) == index['count'] and whole.hexdigest() == index['ordered_records_sha256'],
                  'Snapshot total/order differs')
    route.require(cl.snapshot(values) == values, 'Current inputs differ from completed restoration')
    return values


def run(route, cl, old, ci, bound):
    home, boot, boot_row, saved, baseline_row, observed = verified(route, old, ci, bound)
    verification, verification_row = old.load(home, 'verified.json')
    route.require(verification['context'] == boot['context'] and verification['bootstrap'] == boot_row and
                  verification['baseline'] == baseline_row and verification['observed'] == observed,
                  'No fresh verified privileged Bash boundary')
    # The 90-second timer belongs to launcher observation, never to the replay.
    signal.setitimer(signal.ITIMER_REAL, 0)
    if ci['role'] == 'full':
        cache = folder(ci).parent / ('light-eft-handoff-control-cache-' + ci['run_id'] + '-' + ci['run_attempt'] + '-full-producer')
        route.require(not os.path.lexists(cache), 'Producer control-cache prefix exists')
        # Exec the actual source main; its independently preserved export state
        # and captures describe metadata only, never a kernel replay result.
        os.execv('/usr/bin/python3', ['/usr/bin/python3', '-I', '-B', '-X', 'pycache_prefix=' + str(cache),
                                    str(HERE / 'closure_contract.py'), 'export'])
    number = int(os.environ['LIGHTEFT_REPLAY_BATCH']); binding = route.handoff(ci)
    prior = route.previous(ci, number, binding); names = cl.targets()
    actual_number, selected = cl.selected_batch(names)
    route.require(number == actual_number and len(selected) == 189, 'Exact batch differs')
    report = folder(ci).parent / ('light-eft-replay-batch-' + ci['run_id'] + '-' + ci['run_attempt'] + '-' + str(number))
    report.mkdir(mode=0o700, exist_ok=False)
    state = dict(status='FAILED_INCOMPLETE_BATCH', accepted=False, CI_identity=ci,
                 batch=number, completed=0, original_boundary='launcher-only', child_ECHILD_not_asserted=True)
    try:
        # Source-bound actual main invocation, isolated and with a fresh absent
        # control-cache prefix; no bound_spec/main or synthetic context override.
        cache = folder(ci).parent / ('light-eft-handoff-control-cache-' + ci['run_id'] + '-' + ci['run_attempt'] + '-global_replay-' + str(number))
        route.require(not os.path.lexists(cache), 'Control-cache prefix exists')
        with (report / 'restore.stdout').open('xb') as out, (report / 'restore.stderr').open('xb') as err:
            subprocess.run(['/usr/bin/python3', '-I', '-B', '-X', 'pycache_prefix=' + str(cache),
                            str(HERE / 'closure_contract.py'), 'restore'], cwd=ROOT, check=True, stdout=out, stderr=err)
        restore_home = folder(ci).parent / ('light-eft-replay-restore-' + ci['run_id'] + '-' + ci['run_attempt'] + '-' + str(number))
        restored = route.read(restore_home / 'result.json')
        route.require(restored['status'] == 'BATCH_OBJECTS_AND_METADATA_ONLY_NOT_REPLAY_ACCEPTANCE' and
                      restored['CI_identity'] == cl.identity('global_replay') and
                      restored['batch_target_count'] == 189 and restored['manifest_sha256'] == binding['manifest_sha256'],
                      'Restoration is incomplete or from another source/run')
        stable = read_snapshot(route, cl, restore_home / 'inputs-after')
        objects = read_snapshot(route, cl, restore_home / 'restored-inputs')
        tool, tools, roots, kinds = cl.runtime(); claims = cl.prefixes(roots)
        bundle, transport_path, transport_saved, transport_row = cl.transport(cl.identity('global_replay'), cl.controls())
        manifest, metadata_paths, metadata_bytes = cl.load_manifest(bundle, binding['manifest_sha256'])
        route.require(all(str(path) in stable for path in metadata_paths) and
                      metadata_bytes == restored['authenticated_metadata_bytes'] and
                      manifest['payload_bytes'] + metadata_bytes == restored['total_transfer_bytes'] <= cl.PAYLOAD_LIMIT,
                      'Authenticated metadata snapshot/total transfer budget differs')
        nodes, _ = cl.validate_graph(manifest['graph'], names)
        needed, seeds, imported, _ = cl.selection(manifest['graph'], selected)
        route.require(manifest['schema'] == 'LIGHT_SAME_RUN_REPLAY_HANDOFF_V3' and
                      manifest['acquisition_policy'] == cl.ACQUISITION_POLICY and
                      restored['acquisition_policy'] == cl.ACQUISITION_POLICY,
                      'Restored dependency acquisition policy differs')
        package_namespace_before = cl.package_namespace(roots, kinds)
        route.require(package_namespace_before == restored['package_namespace'],
                      'Package namespace changed after authenticated restoration')
        package_paths = cl.reacquired_package_paths(manifest, nodes, roots, kinds)
        route.require(all(str(path) in stable for path in package_paths),
                      'Producer-validated package input was not preserved by restoration')
        available, object_paths = cl.actual_companions(needed, manifest['objects'], roots)
        # Reestablish companion absence as well as presence for loader read-set
        # equivalence; a receipt alone cannot grant acceptance to new files.
        for name in needed:
            route.require(cl.required_suffixes(name, nodes[name], available[name], seeds, imported) ==
                          cl.required_suffixes(name, nodes[name], manifest['objects'][name]['available'], seeds, imported),
                          'Companion read-set changed after restore')
        # LeanChecker rescans all object names for each target and expands
        # descendants, not just top-level namespace claims. Correlate the actual
        # native census/selected expansions with completed restore and again
        # after all checker calls. This remains an observation under the
        # explicit external no-writer boundary, not a transient-writer proof.
        restored_headers = cl.read_json(restore_home / 'confirmed-restored-header-probe/headers.json')
        cl.validate_graph(restored_headers, selected)
        replay_headers = cl.run_probe(report / 'native-before-replay', selected, tool,
                                      cl.identity('global_replay'))
        native_fingerprint = cl.graph_fingerprint(replay_headers)
        route.require(native_fingerprint == cl.graph_fingerprint(restored_headers) and
                      cl.package_census(replay_headers, kinds) ==
                      cl.package_census(manifest['graph'], kinds) and
                      cl.package_namespace(roots, kinds) == package_namespace_before and
                      cl.snapshot(stable) == stable and cl.snapshot(objects) == objects,
                      'Native object census/expansions changed after restoration')
        receipt_hash = hashlib.sha256()
        for offset, name in enumerate(selected):
            route.require(route.controls() == bound and route.identity('global_replay') == ci,
                          'Source/identity changed before checker')
            current = old.observe_lake(dict(os.environ)); old.equivalent(observed, current)
            begun = time.monotonic_ns()
            command = [str(tool / 'bin/leanchecker'), '-v', name]
            # Each subprocess.run starts and waits for a distinct actual checker;
            # no long-lived kernel process or historical result can satisfy it.
            cl.create(report / ('%03d-start.json' % offset), route.encoded(dict(
                      ordinal=offset, module=name, argv=command, started_ns=begun)))
            with (report / ('%03d.stdout' % offset)).open('xb') as out, (report / ('%03d.stderr' % offset)).open('xb') as err:
                child = subprocess.run(command, cwd=ROOT, stdout=out, stderr=err, check=False)
            row = dict(ordinal=offset, module=name, argv=command, started_ns=begun,
                       ended_ns=time.monotonic_ns(), returncode=child.returncode,
                       direct_wait_returned=True, descendants_ECHILD_not_asserted=True)
            raw = route.encoded(row); cl.create(report / ('%03d-result.json' % offset), raw)
            route.require(child.returncode == 0, 'Actual checker failed: ' + name)
            receipt_hash.update(raw); state['completed'] += 1
        replay_after = cl.run_probe(report / 'native-after-replay', selected, tool,
                                    cl.identity('global_replay'))
        route.require(cl.graph_fingerprint(replay_after) == native_fingerprint,
                      'Native census/header/prefix expansion changed across checker phase')
        native_record = dict(qualification='Observed native census/header/expansion equality only; external no-writer required',
                             graph_fingerprint=native_fingerprint,
                             before={name: cl.digest(report / 'native-before-replay' / name)
                                     for name in ['headers.json', 'capture.json']},
                             after={name: cl.digest(report / 'native-after-replay' / name)
                                    for name in ['headers.json', 'capture.json']})
        cl.create(report / 'native-replay-correlation.json', route.encoded(native_record))
        after_available, after_paths = cl.actual_companions(needed, manifest['objects'], roots)
        route.require(state['completed'] == 189 and cl.snapshot(stable) == stable and
                      cl.snapshot(objects) == objects and cl.prefixes(roots) == claims and
                      after_available == available and set(map(str, after_paths)) == set(map(str, object_paths)) and
                      cl.reacquired_package_paths(manifest, nodes, roots, kinds) == package_paths and
                      cl.package_namespace(roots, kinds) == package_namespace_before and
                      cl.package_census(replay_after, kinds) ==
                      cl.package_census(manifest['graph'], kinds) and
                      cl.observation(transport_path) == transport_saved and cl.runtime()[1:] == (tools, roots, kinds) and
                      route.controls() == bound and route.identity('global_replay') == ci and
                      platform(old) == boot['platform'], 'Final no-writer/source/runtime/object correlation differs')
        old.equivalent(observed, old.observe_lake(dict(os.environ)))
        marker = dict(schema='LIGHT_COMPLETE_REPLAY_BATCH_V1', commit=ci['commit'], repository=ci['repository'],
                      run_id=ci['run_id'], run_attempt=ci['run_attempt'], batch=number, offset=189 * (number - 1),
                      count=189, ordered_targets_sha256=hashlib.sha256(('\n'.join(selected) + '\n').encode()).hexdigest(),
                      handoff=binding, previous_coverage_sha256=prior, every_checker_exit_zero=True,
                      fresh_process_count=189, receipts_sha256=receipt_hash.hexdigest(),
                      native_correlation_sha256=cl.digest(report / 'native-replay-correlation.json')['sha256'])
        marker_sha = route.validate_coverage(marker, ci, number, binding, prior)
        cl.create(report / 'coverage.json', route.encoded(marker))
        state.update(status='COMPLETE_BATCH_REPLAY_RESULTS_NOT_FINAL_ACCEPTANCE', coverage_sha256=marker_sha)
        route.output(dict(validated_commit=ci['commit'], coverage=route.encoded(marker).decode().strip(),
                          coverage_sha256=marker_sha))
    except BaseException as error:
        state['failure'] = repr(error); state['partial_evidence_preserved'] = True
        raise
    finally:
        cl.create(report / 'result.json', route.encoded(state))


def main():
    if not (sys.flags.isolated and sys.dont_write_bytecode):
        raise ValueError('Require Python -I -B')
    if signal.getitimer(signal.ITIMER_REAL) != (0.0, 0.0):
        raise ValueError('Existing timer would be replaced')
    def timeout(*_):
        raise TimeoutError('Original launcher observation exceeded 90 seconds')
    previous = signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 90)
    try:
        route, cl, old, bound, ci = dependencies()
        mode = sys.argv[1]
        route.require(mode in ['bootstrap', 'before-lake', 'enter', 'verify', 'run'], 'Finite batch phase required')
        if mode == 'bootstrap': bootstrap(route, old, ci, bound)
        elif mode == 'before-lake': before_lake(route, old, ci, bound)
        elif mode == 'enter': enter(route, old, ci, bound)
        elif mode == 'verify': verify(route, old, ci, bound, sys.argv[2], sys.argv[3])
        else: run(route, cl, old, ci, bound)
    except BaseException as error:
        try:
            home = folder(ci)
            if home.exists():
                old.write(home, 'failure-' + mode + '.json', dict(error=repr(error), observed_ns=time.monotonic_ns()))
        except BaseException:
            pass
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0); signal.signal(signal.SIGALRM, previous)


if __name__ == '__main__':
    main()
