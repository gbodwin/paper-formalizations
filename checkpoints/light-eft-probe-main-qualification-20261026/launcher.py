"""SOURCE ONLY: genuine native HeaderProbe main profile, never a Python fixture.

The native supervisor/limits/lifecycle are unchanged. A separately bound
qualification-only guard admits the exact JSON namespace; production is untouched.
One actual567 metadata capture; no SDK, replay or production acceptance.
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
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ENGINE = ROOT / 'checkpoints/light-eft-canonical-output-adapter-20261020'
WORKFLOW = '.github/workflows/light-eft-probe-main-qualification.yml'
BRANCH = 'refs/heads/light-eft-spanners-checkpoints'
PROBE = 'checkpoints/light-eft-global-replay-batches-20261026/HeaderProbe.lean'
PROBE_SHA = '715aa2055684da6eff491bf4de5d6646275d62c3197ce4d00d5072c9bb794567'
PARENT = 'd2fdf2011ebb97c86bc5840b4df6617a53b8d4f9'
LEAN = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
CHECKER = 'ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def git(*args):
    return subprocess.run(['/usr/bin/git', *args], cwd=ROOT, check=True,
                          capture_output=True, timeout=10).stdout


def main():
    require(sys.flags.isolated and sys.dont_write_bytecode, 'Require Python -I -B')
    e = dict(os.environ); head = e.get('GITHUB_SHA', '')
    require(e.get('GITHUB_ACTIONS') == 'true' and
            e.get('GITHUB_REPOSITORY') == 'gbodwin/paper-formalizations' and
            e.get('GITHUB_REF') == BRANCH and e.get('GITHUB_EVENT_NAME') == 'push' and
            e.get('LIGHTEFT_HANDOFF_PURPOSE') == 'reacquisition_qualification' and
            e.get('LIGHTEFT_REACQUISITION_ROLE') in ['producer', 'consumer'] and
            e.get('GITHUB_JOB') == {'producer': 'native_probe_main',
                'consumer': 'native_reacquisition_consumer'}.get(e.get('LIGHTEFT_REACQUISITION_ROLE')) and e.get('LEAN_NUM_THREADS') == '1',
            'Wrong actual native qualification source/job')
    require(len(head) == 40 and all(c in '0123456789abcdef' for c in head) and
            all(e.get(k, '').isdecimal() and int(e[k]) > 0
                for k in ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Invalid source/run/attempt')
    repo = e['GITHUB_REPOSITORY']
    require(e.get('GITHUB_WORKFLOW') == 'LightEFT probe main profile qualification' and
            e.get('GITHUB_WORKFLOW_SHA') == head and
            e.get('GITHUB_WORKFLOW_REF') == repo + '/' + WORKFLOW + '@' + BRANCH and
            e.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY') == repo and
            e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == WORKFLOW and
            e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == head and
            e.get('LIGHTEFT_JOB_WORKFLOW_REF') in
            [repo + '/' + WORKFLOW + '@' + BRANCH, repo + '/' + WORKFLOW + '@' + head],
            'Actual qualification workflow differs')
    identity = {k: e[k] for k in ['GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_REF',
                'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB', 'GITHUB_WORKFLOW',
                'GITHUB_WORKFLOW_SHA', 'GITHUB_WORKFLOW_REF', 'LEAN_NUM_THREADS',
                'LIGHTEFT_JOB_WORKFLOW_REPOSITORY', 'LIGHTEFT_JOB_WORKFLOW_PATH',
                'LIGHTEFT_JOB_WORKFLOW_SHA', 'LIGHTEFT_JOB_WORKFLOW_REF', 'LIGHTEFT_REACQUISITION_ROLE']}
    temp = Path(e['RUNNER_TEMP'])
    require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(), 'Unsafe temporary root')
    root = temp / ('light-eft-probe-main-profile-' + e['GITHUB_RUN_ID'] + '-' + e['GITHUB_RUN_ATTEMPT'])
    root.mkdir(mode=0o700, exist_ok=False)
    require(signal.getitimer(signal.ITIMER_REAL) == (0.0, 0.0), 'Existing source/admission alarm')
    previous = signal.getsignal(signal.SIGALRM)
    def expired(*_):
        raise TimeoutError('Native qualification source/admission exceeded90seconds')
    signal.signal(signal.SIGALRM, expired); signal.setitimer(signal.ITIMER_REAL, 90)
    try:
        raw = (HERE / 'bindings.json').read_bytes()
        require(hashlib.sha256(raw).hexdigest() == e.get('LIGHTEFT_QUALIFICATION_BINDINGS_SHA'),
                'Exact qualification bindings differ')
        rows = json.loads(raw)['files']
        require(0 < len(rows) <= 80 and len(rows) == len({r['path'] for r in rows}) and
                sum(r['bytes'] for r in rows) <= 2 * 1024**2, 'Finite source binding allowance exceeded')
        os.environ['PATH'] = '/usr/bin:/bin'
        require(git('rev-parse', 'HEAD').decode().strip() == head and
                git('show', '-s', '--format=%P', 'HEAD').decode().strip() == PARENT and
                not git('status', '--porcelain'), 'Exact clean sole-parent checkout differs')
        require(Path.cwd().resolve() == ROOT, 'Wrong working directory')
        capture_guard_paths = []
        def authenticate():
            require(git('rev-parse', 'HEAD').decode().strip() == head and
                    git('show', '-s', '--format=%P', 'HEAD').decode().strip() == PARENT and
                    not git('status', '--porcelain'), 'Source HEAD/parent/cleanliness changed')
            require(os.getuid() == os.geteuid() and os.getgid() == os.getegid(),
                    'Real/effective native owner identity differs')
            for row in rows:
                rel = Path(row['path']); p = ROOT / rel
                require(not rel.is_absolute() and '..' not in rel.parts and
                        not any(q.is_symlink() for q in [p, *p.parents]), 'Unsafe bound source path')
                s = p.lstat(); require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1 and
                                      s.st_size == row['bytes'], 'Nonregular source binding')
                b = p.read_bytes()
                require(hashlib.sha256(b).hexdigest() == row['sha256'] and
                        git('show', 'HEAD:' + rel.as_posix()) == b, 'Source hash/Git binding differs')
            wf = ROOT / WORKFLOW
            require(not any(q.is_symlink() for q in [wf, *wf.parents]) and
                    wf.read_bytes() == git('show', 'HEAD:' + WORKFLOW), 'Actual workflow bytes differ')
            require({k: os.environ.get(k) for k in identity} == identity,
                    'Native qualification identity changed')
            if capture_guard_paths:
                require(caller_capture.validate_capture(e) == capture_guard_paths and
                        os.environ.get('LIGHTEFT_LAKE_CAPTURE_DIR') == e.get('LIGHTEFT_LAKE_CAPTURE_DIR'),
                        'Same-process waited Lake capture changed')
        authenticate()
        require((ROOT / PROBE).stat().st_size == 5895 and
                hashlib.sha256((ROOT / PROBE).read_bytes()).hexdigest() == PROBE_SHA,
                'Actual production HeaderProbe source differs')
        profile = json.loads((HERE / 'profile.json').read_bytes())
        require(profile['scope'] == 'NATIVE_HEADER_PROBE_MAIN_567_PROFILE_ONLY' and
                profile['synthetic_fixture'] is False and profile['target_count'] == 567 and
                profile['production_acceptance'] is False, 'Wrong finite metadata profile')
        sys.pycache_prefix = str(root / 'absent-python-cache')
        require(not os.path.lexists(sys.pycache_prefix) and
                all(n not in sys.modules for n in ['child_runner', 'output_guards', 'closure_contract', 'lake_capture', 'path_config', 'qualification_adapter']),
                'Inherited qualification module/cache')
        replay = (ROOT / PROBE).parent
        sys.path[:0] = [str(HERE), str(ENGINE), str(ROOT / 'scripts'), str(replay)]
        from contracts import bind, save, unchanged
        from ci_inventory import CIInventory, CIIdentityGuard
        from ci_accounting import CIAccounting
        from ci_lease import CILease
        from LightEFTCgroup import memory_snapshot
        import output_guards as qualified_outputs
        import child_runner
        from pilot_child import LIMITS
        import closure_contract as cl
        import qualification_adapter as qualification
        import lake_capture as caller_capture
        import path_config as path_representation
        require(Path(qualified_outputs.__file__).resolve() == HERE / 'output_guards.py' and
                child_runner.audit_output_errors is qualified_outputs.runtime_errors and
                Path(cl.__file__).resolve() == replay / 'closure_contract.py',
                'Actual qualification module source binding differs')
        require(Path(caller_capture.__file__).resolve() == HERE / 'lake_capture.py',
                'Actual Lake capture validator source differs')
        require(Path(path_representation.__file__).resolve() == HERE / 'path_config.py',
                'Actual path/config adapter source differs')
        capture_guard_paths = caller_capture.validate_capture(e)
        require(LIMITS['RLIMIT_AS'] == 12 * 1024**3 and LIMITS['RLIMIT_CPU'] == 60 and
                LIMITS['RLIMIT_CORE'] == 0 and child_runner.DEADLINE == 90 and
                child_runner.PREFLIGHT_DEADLINE == 300 and child_runner.RSS_STOP == 6 * 1024**3 and
                child_runner.ANON_GROWTH_STOP == 3 * 1024**3 and
                child_runner.STOP_HEADROOM == 1024**3 and child_runner.INTERVAL == .1,
                'Accepted native resource/lifecycle envelope changed')
        # These are data/runtime functions, not a forged full/global producer entry.
        production_controls = cl.controls()
        require(Path(qualification.__file__).resolve() == replay / 'qualification_adapter.py' and
                qualification.identity(cl) == identity, 'Explicit qualification adapter identity differs')
        names = cl.targets()
        tool, tools, roots, kinds = cl.runtime()
        require(len(names) == 567 and hashlib.sha256(('\n'.join(names) + '\n').encode()).hexdigest() ==
                profile['ordered_targets_sha256'], 'Original full target case differs')
        require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0' and
                tools['lean']['sha256'] == LEAN and tools['leanchecker']['sha256'] == CHECKER,
                'Actual installed toolchain differs')
        rawsrc = e.get('LEAN_SRC_PATH', '')
        require(rawsrc and all(rawsrc.split(':')), 'Missing actual Lake source path')
        srcroots = [(Path(p) if Path(p).is_absolute() else ROOT / p).resolve(strict=True)
                    for p in rawsrc.split(':')]
        require(all(p.is_dir() and
                    (p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(tool / 'src/lean'))
                    for p in srcroots), 'Source search roots outside exact checkout/toolchain')
        source = {str(ROOT / r['path']): bind(ROOT / r['path'], r) for r in rows}
        for p in [*capture_guard_paths, HERE / 'bindings.json', ROOT / WORKFLOW,
                  *[tool / 'bin' / n for n in ['lean', 'leanchecker', 'lake']]]:
            source[str(p)] = bind(p)
        account = CIAccounting(memory_snapshot); baseline = account.sample()
        save(root / 'initial-admission-sample.json', baseline)
        require(baseline['headroom'] >= 8 * 1024**3 and baseline['system_available'] >= 8 * 1024**3,
                'Fresh outer8GiB constrained/host admission failed')
        ps_paths = caller_capture.process_snapshot(root)
        for p in ps_paths:
            source[str(p)] = bind(p)
        idle_record = {}
        try:
            # Same unchanged guard/decision; snapshot is evidence, never a whitelist.
            child_runner.assert_idle('native-probe-main-before-claim', idle_record)
        except BaseException as idle_error:
            save(root / 'idle-guard-refusal.json', dict(error=repr(idle_error),
                 pre_guard_snapshot={str(p): source[str(p)] for p in ps_paths},
                 monotonic_ns=time.monotonic_ns(),
                 snapshot_not_atomic_with_guard=True, no_exclusive_PID_attribution=True))
            raise
        require(len(json.dumps(idle_record).encode()) <= 65536, 'Idle evidence allowance exceeded')
        save(root / 'idle-guard-success.json', idle_record)
        source[str(root / 'idle-guard-success.json')] = bind(root / 'idle-guard-success.json')
        require(sum(p.stat().st_size for p in [*capture_guard_paths, *ps_paths,
                    root / 'idle-guard-success.json']) <= 1024**2,
                'Public capture/process evidence exceeds1MiB')
        consumer_state = None
        if identity['LIGHTEFT_REACQUISITION_ROLE'] == 'consumer':
            # Authenticated data preparation, outside later native-child admission.
            consumer_state = qualification.prepare_consumer(
                cl, identity, root, tool, tools, roots, kinds, names, production_controls)
            for path in consumer_state['protected_paths']:
                source[str(path)] = bind(path)
        work = root / 'work'; work.mkdir(mode=0o700)
        objects = work / 'objects'; objects.mkdir(mode=0o700)
        audit = work / 'empty-audit'; audit.mkdir(mode=0o700)
        graphdir = work / 'graph'; graphdir.mkdir(mode=0o700)
        request = work / 'request.json'; output = graphdir / 'headers.json'
        raw = cl.encoded(dict(targets=names)); require(len(raw) <= 1024**2, 'Probe request exceeds source allowance')
        cl.create(request, raw); source[str(request)] = bind(request)
        expected_sources = srcroots + [(tool / 'src/lean/lake').resolve(strict=True),
                                       (tool / 'src/lean').resolve(strict=True)]
        source_defaults = [str(tool / 'bin/../src/lean/lake'), str(tool / 'bin/../src/lean')]
        original_objects = [str(Path(x) if Path(x).is_absolute() else ROOT / x)
                            for x in e['LEAN_PATH'].split(':')] + [str(tool / 'lib/lean')]
        original_sources = [str(Path(x) if Path(x).is_absolute() else ROOT / x)
                            for x in rawsrc.split(':')] + source_defaults
        absent_allowed = [str(ROOT / '.lake/packages' / name / '.lake/build/lib/lean')
                          for name in cl.PINS]
        object_path, object_witness = path_representation.spell_entries(
            roots, work, 'LEAN_PATH', len(roots) - 1, [str(tool / 'lib/lean')],
            absent_allowed=absent_allowed, original_spellings=original_objects)
        source_path, source_witness = path_representation.spell_entries(
            expected_sources, work, 'LEAN_SRC_PATH', len(srcroots), source_defaults,
            original_spellings=original_sources)
        # Explicit public Lean environment only. Same namespace, no credential dump.
        plan = dict(stage='resolve', module='HeaderProbeMain567',
                    argv=[str(tool / 'bin/lean'), '-j1', '-s65536', '-M5120',
                          '-DautoImplicit=false', '-DwarningAsError=true', '--run',
                          str(ROOT / PROBE), 'request.json', 'graph/headers.json'],
                    env=dict(LANG='C.UTF-8', LC_ALL='C.UTF-8', LEAN_NUM_THREADS='1',
                             LEAN_SYSROOT=str(tool), LEAN_PATH=object_path,
                             LEAN_SRC_PATH=source_path,
                             MIMALLOC_ARENA_RESERVE='128MiB', MIMALLOC_VERBOSE='1'), cwd=str(work))
        frozen = json.dumps(plan, sort_keys=True)
        path_representation.verify_arguments(plan, work, ROOT / PROBE, request, output)
        configuration, config_evidence = path_representation.preserve_attempt(
            plan, root, caller_capture.create, save)
        path_witness = dict(schema='SAME_CWD_PATH_SPELLINGS_V2_ABSENCE', cwd=str(work),
             object_entries=object_witness, source_entries=source_witness,
             all_entries_order_duplicates_preserved=True,
             argv=dict(program=str(ROOT / PROBE), request_absolute=str(request),
                       request_spelling='request.json', output_absolute=str(output),
                       output_spelling='graph/headers.json'),
             exact_config_bytes=len(configuration))
        witness_bytes = (json.dumps(path_witness) + '\n').encode()
        save(root / 'path-encoding-attempt.json', dict(bytes=len(witness_bytes),
             sha256=hashlib.sha256(witness_bytes).hexdigest(), bound=65536,
             actual_save_encoding=True, no_runtime_fit_claim=True))
        require(len(witness_bytes) <= 65536, 'Path evidence exceeds unchanged64KiB')
        caller_capture.create(root / 'path-encoding.json', witness_bytes)
        for p in [*config_evidence, root / 'path-encoding.json', root / 'path-encoding-attempt.json']:
            source[str(p)] = bind(p)
        require(sum(p.stat().st_size for p in [*capture_guard_paths, *ps_paths,
                    root / 'idle-guard-success.json', *config_evidence, root / 'path-encoding.json',
                    root / 'path-encoding-attempt.json']) <= 1024**2,
                'Selected public/config evidence exceeds unchanged1MiB allowance')
        save(root / 'submitted-plan.json', dict(identity=identity, plan=plan, profile=profile,
             source_bindings=source, actual_tools=tools, actual_roots=list(map(str, roots)),
             ordinary_setup_not_child_admission=True, production_acceptance=False))
        prefix_before = cl.prefixes(roots)
        # Namespace order/multiplicity is semantic; inventory visits each physical root once.
        inventory_roots = path_representation.physical_roots(object_witness, work)
        require(tool / 'lib/lean' in inventory_roots, 'Required toolchain runtime root is absent')
        save(root / 'physical-inventory-roots.json', dict(
            ordered_effective_roots=list(map(str, roots)),
            unique_physical_roots=list(map(str, inventory_roots)),
            absent_slots=[r['index'] for r in object_witness['slots']
                          if object_witness['roots'][r['absolute']]['state'] == 'absent'],
            namespace_witness=bind(root / 'path-encoding.json'), semantic_slots_never_dropped=True))

        def add_source_inputs(inputs):
            # Complete tracked package Lean source membership is discovered from pinned Git.
            paths = {ROOT / r['path'] for b in cl.read_json(replay / 'targets.json')['batches'] for r in b['targets']}
            for package in cl.PINS:
                base = ROOT / '.lake/packages' / package
                for rel in cl.git('ls-files', '-z', '--', '*.lean', cwd=base).split(b'\0'):
                    if rel:
                        text = rel.decode(); cl.safe_relative(text); paths.add(base / text)
            paths.update((tool / 'src/lean').rglob('*.lean'))
            require(len(paths) <= 200000, 'Source membership census exceeds finite allowance')
            for p in sorted(paths, key=str):
                require(p.is_file() and not any(q.is_symlink() for q in [p, *p.parents]),
                        'Unsafe native source input')
                inputs[str(p)] = bind(p)

        class NativeContext:
            fixture = False; source_commit = head; wrapper_commit = head
            def __init__(self, lease):
                self.lease = lease; self.lock = lease.file; self.acquired_ns = lease.acquired_ns
                self.preservation_failed = False; self.guard = None; self.inputs = dict(source)
                self.inventory = CIInventory(inventory_roots, tool, bind); self.api_exercised = False
            def visible_gate(self, p):
                return 8 * 1024**3
            def verify(self, p):
                require(json.dumps(p, sort_keys=True) == frozen and p['stage'] == 'resolve' and
                        p['argv'][0] == str(tool / 'bin/lean') and p['argv'][6:] ==
                        ['--run', str(ROOT / PROBE), 'request.json', 'graph/headers.json'] and
                        path_representation.config_bytes(p) == configuration,
                        'Changed actual metadata command/env/resource class')
                path_representation.verify_arguments(p, work, ROOT / PROBE, request, output)
                path_representation.verify_entries(p['env']['LEAN_PATH'], roots[:-1], work, object_witness)
                path_representation.verify_entries(p['env']['LEAN_SRC_PATH'], srcroots, work, source_witness)
                self.lease.check(); authenticate(); unchanged(source)
                require(not list(audit.iterdir()), 'Unexpected audit export')
            def before_child(self, p, receipt, persist):
                self.verify(p)
                receipt.update(native_qualification='NATIVE_HEADER_PROBE_MAIN_567_PROFILE_ONLY',
                    API_runtime_requested=True, qualification_only=True, production_acceptance=False,
                    synthetic_fixture=False, working_directory=str(work), planned_command=plan,
                    legacy_scope_field_not_current_import_authority=True,
                    output_guard_implementation=bind(HERE / 'output_guards.py'),
                    output_guard_spec=dict(stage='resolve', objects=str(objects), audit=str(audit),
                        protected=self.inputs, metadata_only=dict(identity=identity, program=str(ROOT / PROBE),
                            request=str(request), output=str(output), ordered_targets_sha256=profile['ordered_targets_sha256'],
                            namespace_witness=str(root / 'path-encoding.json'))))
                persist()
                add_source_inputs(self.inputs)
                observed = self.inventory.scan()
                self.inputs.update(observed['semantic']); self.inputs.update(observed['excluded'])
                members = {name: set(files) | {d for d in observed['directories']
                           if d != name and Path(d).is_relative_to(name)}
                           for name, files in observed['members'].items()}
                self.guard = CIIdentityGuard(self.inputs, members, observed['directories'])
                ordered = sorted(self.inputs.items()); chunks = []
                for offset in range(0, len(ordered), 64):
                    path = root / ('inputs-%04d.json' % (offset // 64))
                    save(path, ordered[offset:offset + 64]); chunks.append(bind(path))
                save(root / 'inputs-index.json', dict(count=len(ordered), chunks=chunks,
                     qualification='Fresh same-run actual namespace/source inputs, no authenticated cache provenance'))
                receipt['native_input_files'] = len(self.inputs); persist()
            def prepare_child(self, p, receipt, persist, accounting):
                self.verify(p); child_runner.assert_idle('native-probe-main-preflight', receipt)
                self.inventory.scan(); self.guard.verify()
                now = accounting.sample(); child_runner.check_memory(now, baseline, 8 * 1024**3)
                require(now['system_available'] >= 8 * 1024**3 and
                        shutil.disk_usage(work).free > 2 * 1024**3, 'Fresh host/disk admission failed')
                receipt['admission'] = now; persist(); return now
            def preexec(self, p, receipt, persist):
                self.verify(p); self.guard.verify(); unchanged(source)
                now = account.sample(); child_runner.check_memory(now, baseline, 8 * 1024**3)
                free = shutil.disk_usage(work).free
                require(now['system_available'] >= 8 * 1024**3 and free > 2 * 1024**3,
                        'Fresh preexec host/disk admission failed')
                receipt.update(preexec_binding_verified=True, preexec_disk_bytes=free,
                               preexec_native_qualification_admission=now); persist()
            def profile_graph(self, receipt, phase):
                phase('read-raw-graph')
                raw_graph = cl.read_json(output)
                phase('canonical-graph')
                graph, normalization = path_representation.canonical_graph(
                    raw_graph, work, roots, expected_sources, self.inputs, object_witness, source_witness)
                normalization['raw_graph'] = bind(output)
                save(root / 'graph-path-normalization.json', normalization)
                require(normalization.get('schema') == 'RAW_GRAPH_CANONICAL_PATH_VIEW_V2' and
                        normalization.get('canonical_view_encoding') == dict(
                            tag='SORTED_COMPACT_DEFAULT_ASCII_JSON_UTF8_NO_NEWLINE_V1',
                            sort_keys=True, ensure_ascii=True, separators=[',', ':'],
                            text_encoding='utf-8', trailing_newline=False),
                        'Canonical graph view encoding binding differs')
                require(normalization['canonical_view_bytes'] <= 16 * 1024**2,
                        'Canonical graph view exceeds unchanged16MiB graph allowance')
                phase('validate-graph')
                nodes, _ = cl.validate_graph(graph, names)
                self.api_exercised = True
                phase('prefix-census')
                require(cl.prefixes(roots) == prefix_before, 'Object prefix census changed')
                phase('closure-inventory')
                objs, sources, claims, paths = cl.inventory(graph, names, tool, roots, kinds)
                phase('protected-companions')
                selected = {}
                for path in set(map(str, paths)):
                    require(path in self.inputs and not self.inputs[path].get('metadata_only'),
                            'Closure input was not protected before native exec')
                    selected[path] = self.inputs[path]
                # Every complete family binding must agree with the pre-exec inventory.
                for name, row in objs.items():
                    base = roots[row['root']] / row['relative']
                    for suffix, value in row['available'].items():
                        if value is not None:
                            old = selected[str(cl.part_path(base, suffix))]
                            require(all(old[k] == value[k] for k in ['bytes', 'sha256']),
                                    'Companion bytes changed during capture')
                phase('object-namespace')
                path_representation.verify_namespace(object_witness, work)
                phase('source-namespace')
                path_representation.verify_namespace(source_witness, work)
                phase('profile-guard')
                self.guard.verify()
                phase('profile-source')
                unchanged(source)
                phase('write-profile')
                payload = sum(r['bytes'] for r in selected.values())
                folder = root / 'closure-profile'; folder.mkdir(mode=0o700)
                chunks = []
                # selected is unchanged throughout this loop; preserve the exact
                # former per-chunk ordering without repeating the identical sort.
                ordered_selected = sorted(selected.items())
                for offset in range(0, len(selected), 64):
                    path = folder / ('bindings-%04d.json' % (offset // 64))
                    save(path, ordered_selected[offset:offset + 64]); chunks.append(bind(path))
                out = dict(schema='NATIVE_567_GRAPH_PROFILE_ONLY_V1', graph=bind(output),
                    path_normalization=bind(root / 'graph-path-normalization.json'),
                     target_count=567, nodes=len(nodes), census=len(graph['census']),
                    regions_retained=graph['regions_retained'], actual_roots=list(map(str, roots)),
                    prefix_claims=claims, closure_files=len(selected), payload_bytes=payload,
                    payload_bytes_legacy_protected_inventory_not_transfer=True,
                    closure_chunks=chunks, actual_tools=tools, actual_package_pins=cl.PINS,
                    actual_case_only=True, batch_native_cases=0, export_or_transport_invoked=False,
                    no_authenticated_cache_provenance=True, production_acceptance=False)
                save(root / 'graph-profile.json', out)  # Preserve measured refusal before evaluating ceiling.
                if identity['LIGHTEFT_REACQUISITION_ROLE'] == 'producer':
                    phase('qualification-seal')
                    result = qualification.seal_observed(cl, graph, names, tool, tools,
                        roots, kinds, production_controls, identity, root, receipt, self.inputs,
                        (objs, sources, claims, paths))
                else:
                    phase('qualification-compare')
                    result = qualification.verify_consumer(cl, identity, graph, names, tool,
                        tools, roots, kinds, production_controls, consumer_state)
                # The broad protected input profile is not the transfer payload.
                # The V3 helpers enforce project+allmetadata+attestation TOTAL1GiB.
                phase('final-guard')
                self.guard.verify()
                phase('final-source')
                unchanged(source)
                phase('write-qualification-result')
                save(root / 'qualification-data-result.json', result)
                return dict(out, explicit_reacquisition_qualification=result)
            def after_child(self, p, receipt, persist):
                self.verify(p)
                if self.guard is not None:
                    self.inventory.scan(); self.guard.verify()
                if receipt.get('exit') == 0 and 'failure' not in receipt:
                    # Finite post-capture validation; no new native process or export.
                    prior = signal.getsignal(signal.SIGALRM)
                    timing = dict(schema='POST_CAPTURE_PHASE_TIMING_V1',
                        aggregate_cap_seconds=90, maximum_marks=16,
                        state='running', active_phase=None, marks=[])
                    receipt['post_capture_phase_timing'] = timing
                    phase_names = ('read-raw-graph', 'canonical-graph', 'validate-graph',
                        'prefix-census', 'closure-inventory', 'protected-companions',
                        'object-namespace', 'source-namespace', 'profile-guard',
                        'profile-source', 'write-profile', 'qualification-seal',
                        'qualification-compare', 'final-guard', 'final-source',
                        'write-qualification-result', 'returned')
                    def phase(name):
                        require(name in phase_names and len(timing['marks']) < 16,
                                'Post-capture timing mark bound exceeded')
                        now = time.monotonic_ns()
                        timing['active_phase'] = name
                        timing['marks'].append(dict(phase=name, started_ns=now,
                            since_start_ns=now - timing['started_ns']))
                        persist()  # Fixed phase transitions only, never per chunk/file.
                    def post_timeout(*_):
                        raise TimeoutError('Post-capture validation90s')
                    signal.signal(signal.SIGALRM, post_timeout)
                    signal.setitimer(signal.ITIMER_REAL, 90)
                    timing['started_ns'] = time.monotonic_ns()
                    try:
                        self.outputs = self.profile_graph(receipt, phase)
                        phase('returned')
                        timing['state'] = 'completed'
                    except BaseException as error:
                        timing['state'] = 'failed'
                        timing['failure_phase'] = timing['active_phase']
                        timing['failure_type'] = type(error).__name__
                        raise
                    finally:
                        timing['ended_ns'] = time.monotonic_ns()
                        timing['elapsed_ns'] = timing['ended_ns'] - timing['started_ns']
                        signal.setitimer(signal.ITIMER_REAL, 0); signal.signal(signal.SIGALRM, prior)
                    receipt['native_metadata_graph'] = self.outputs
                receipt['native_inventory_completed'] = self.guard is not None
                receipt['between_child_preservation_passed'] = self.guard is not None
                receipt['API_runtime_exercised'] = self.api_exercised; persist()
            def complete_log(self, path, receipt, persist):
                receipt.setdefault('completed_logs', {})[path.name] = bind(path); persist()
            def output_summary(self):
                return dict(production_acceptance=False, API_runtime_exercised=self.api_exercised,
                            native_graph_profile=getattr(self, 'outputs', {}))
    except BaseException as error:
        partial = getattr(error, 'partial', None)
        if partial is None:
            partial = getattr(locals().get('account'), 'last_partial', None)
        (root / 'source-admission-failure.json').write_text(json.dumps(dict(
            error=repr(error), partial_accounting=partial, traceback=traceback.format_exc(),
            qualification_only=True), indent=2) + '\n')
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0); signal.signal(signal.SIGALRM, previous)
    try:
        with CILease(root, save, authenticate) as lease:
            ctx = NativeContext(lease)
            receipt = child_runner.run_child(plan, work, root / 'runtime', ctx, accounting=account)
            require(receipt['state'] == 'finished' and receipt['exit'] == 0 and
                    receipt.get('synthetic_fixture') is False and receipt.get('kernel_limits_verified') is True and
                    receipt.get('direct_reaped') is True and receipt.get('kernel_no_children_verified') is True and
                    receipt.get('all_descendants_gone') is True and not receipt.get('failure') and
                    not receipt.get('cleanup_errors'), 'Incomplete genuine native child lifecycle')
        require(lease.record['state'] == 'released' and lease.record.get('kernel_echild') is True and
                not lease.record.get('release_errors'), 'Incomplete genuine lease release')
        if identity['LIGHTEFT_REACQUISITION_ROLE'] == 'producer':
            qualification.finish_producer(cl, identity, root, receipt, lease.record,
                ctx.outputs['explicit_reacquisition_qualification'])
        else:
            qualification.clean_lifecycle(cl, receipt, lease.record)
        save(root / 'result-summary.json', dict(native_probe_main_profile_passed=True,
             qualification_only=True, synthetic_fixture=False, API_runtime_exercised=True,
             production_acceptance=False, identity=identity, attempt=receipt['attempt_id'],
             lease=lease.record, outputs=ctx.outputs))
    except BaseException as error:
        save(root / 'qualification-failure.json', dict(error=repr(error), traceback=traceback.format_exc(),
             qualification_only=True, production_acceptance=False))
        raise


if __name__ == '__main__':
    main()
