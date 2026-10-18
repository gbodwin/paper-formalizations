"""Finite batch bindings, exact plans, between-child preservation and output ledger."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from shared_preservation import inspect, encode, signature, utc
from one_time_extension import ExtendedFrozenInputs as FrozenInputs, selected as scope_selected
import child_runner as child
import pilot_cache_advice as advice

B = Path(__file__).resolve().parent
R = B.parents[1]
TOOL = Path('/workspace/toolchains/lean-4.34.0-linux')
PACKAGES = Path('/workspace/paper-formalizations/.lake/packages')
PLAN_RAW = (B / 'PLAN.json').read_bytes()
PLAN_SHA = hashlib.sha256(PLAN_RAW).hexdigest()
PLAN = json.loads(PLAN_RAW)
WORK = R / PLAN['retained_work_root']
OUT = WORK / 'objects'
SOURCE = PLAN['source_commit']
LEAN = TOOL / 'bin/lean'
CHECKER = TOOL / 'bin/leanchecker'
RESOLVER = R / 'scripts/LightEFTResolveCheckerTarget.lean'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')


def digest(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


class Batch:
    fixture_only = False
    def __init__(self, lock, lease):
        self.lock = lock
        self.acquired_ns = lease.record['acquired_ns']
        self.preservation_failed = False
        self.modules = {x['module']: x for x in PLAN['modules']}
        self.graph = json.loads((R / PLAN['source_graph_path']).read_text())
        self.graph_by_name = {x['module']: x for x in self.graph}
        self.pins = json.loads((R / 'lake-manifest.json').read_text())['packages']
        self.roots = [PACKAGES / x['name'] / '.lake/build/lib/lean' for x in self.pins
                      if (PACKAGES / x['name'] / '.lake/build/lib/lean').is_dir()] + [TOOL / 'lib/lean']
        self.project_roots = [R / 'Light Edge Fault Tolerant Graph Spanners', R / 'An Alternate Proof of Near-Optimal Light Spanners']
        self.source_membership = self.project_sources()
        self.ledger = {}
        self.partial_outputs = {}
        self.resolutions = {}
        self.partial_resolutions = {}
        self.ledger_version = 0
        self.small = []
        self.expanded_rows = scope_selected(R, PLAN)

    def project_sources(self):
        files = set()
        for root, ns in zip(self.project_roots, ['LightEFTSpanners', 'LightSpanners'], strict=True):
            files.update((root / ns).rglob('*.lean'))
            p = root / (ns + '.lean')
            if p.exists():
                files.add(p)
        return files

    def execution_paths(self):
        files = set(self.source_membership)
        files.update(B.glob('*.py'))
        files.update(Path(name) for name in self.expanded_rows)
        files.update(R / row['path'] for row in PLAN['expanded_advice_manifests'] + PLAN['new_archive_authorities'] + PLAN['new_data_manifests'])
        files.update([B / 'expanded-scope-selection.json', B / 'retained-root-binding.json', *[Path(row['path']) for row in PLAN['retained_resolution_bindings']]])
        files.update([B / 'PLAN.json', B / 'toolchain-object-advice.json', LEAN, CHECKER,
                      RESOLVER, Path(sys.executable).resolve(), R / 'scripts/LightEFTProcessLifecycle.py',
                      R / 'lake-manifest.json', R / 'lean-toolchain', R / PLAN['source_graph_path'],
                      R / 'checkpoints/light-eft-batch50-entries22-71-20261017/inputs.jsonl',
                      *[R / x['path'] for x in PLAN['accepted_seeds']], *[R / x['path'] for x in PLAN['accepted_seed_evidence']], advice.INVENTORY, R / PLAN['recovery_scope_reference'],
                      R / 'checkpoints/light-eft-finitelaw-finite-recovery-20261017/evidence/replay/receipt.json', R / 'checkpoints/light-eft-batch20-20261017/final-content-verification.json', R / 'checkpoints/light-eft-batch20-20261017/output-records.jsonl', R / 'checkpoints/light-eft-batch20-20261017/attempts/001-LightEFTSpanners.AdaptiveFiniteLaw-compile/receipt.json'])
        for pin in self.pins:
            files.update((PACKAGES / pin['name']).rglob('*.lean'))
        for root in self.roots:
            if root.is_symlink():
                raise RuntimeError('Symlink search root')
            for p in root.rglob('*'):
                if p.is_symlink():
                    raise RuntimeError('Symlink in frozen search tree')
                if p.is_file() and (str(p).endswith(SUFFIXES) or '.so' in p.name):
                    if p.relative_to(root).parts[0].split('.')[0] in ('LightEFTSpanners', 'LightSpanners'):
                        raise RuntimeError('Inherited project object in dependency tree')
                    files.add(p)
        return files

    def check_pins(self):
        for p in self.pins:
            directory = PACKAGES / p['name']
            if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip() != p['rev']:
                raise RuntimeError('Dependency revision changed: ' + p['name'])
            if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=directory):
                raise RuntimeError('Dependency tracked source changed: ' + p['name'])

    def initialize(self):
        self.check_pins()
        if not WORK.is_dir() or WORK.is_symlink():
            raise RuntimeError('Retained work root unavailable or symlink')
        ledger_path = R / PLAN['retained_output_ledger_path']
        authority = next(row for row in PLAN['accepted_seed_evidence'] if row['path'] == PLAN['retained_output_ledger_path'])
        if digest(ledger_path) != authority['sha256']:
            raise RuntimeError('Retained ledger authority changed')
        initial = json.loads(ledger_path.read_text().splitlines()[-1])['objects']
        if len(initial) != 371 or {row['path'] for row in initial} != {str(self.object_path(row['module'])) for row in PLAN['accepted_seeds']}:
            raise RuntimeError('Retained objects differ from 371 accepted qualified ordinary chains')
        self.ledger = {row['path']: row for row in initial}
        for binding in PLAN['retained_resolution_bindings']:
            resolution = Path(binding['path'])
            if inspect(resolution, {'role': binding['role']}) != binding:
                raise RuntimeError('Accepted retained resolution content/identity changed')
            data = json.loads(resolution.read_text())
            if data['count'] != 1 or data['resolved'] != [{'module': data['target'], 'object': str(self.object_path(data['target']))}]:
                raise RuntimeError('Accepted resolution no longer names the retained exact object')
            self.resolutions[str(resolution)] = binding
        entries = list(WORK.rglob('*'))
        if any(path.is_symlink() for path in entries):
            raise RuntimeError('Symlink in retained root')
        actual = {str(path) for path in entries if path.is_file()}
        if actual != set(PLAN['retained_membership_files']):
            raise RuntimeError('Retained root file membership differs from accepted state')
        directories = {str(parent) for name in actual for parent in Path(name).parents if parent != WORK and WORK in parent.parents}
        if {str(path) for path in entries if path.is_dir()} != directories:
            raise RuntimeError('Unexpected retained root directory membership')
        self.check_objects()
        self.check_work_membership()
        (B / 'retained-root-binding.json').write_text(json.dumps({'root': str(WORK), 'files': sorted(actual), 'directories': sorted(directories), 'objects': initial, 'resolutions': list(self.resolutions.values()), 'exact_initial_membership': True}, indent=2) + '\n')
        self.save_ledger('retained-existing-371-objects-and-300-resolutions')
        execution = self.execution_paths()
        self.execution_membership = execution
        prior = advice.load_inventory()
        specs = {}
        for p in execution:
            spec = {'role': 'execution_input'}
            old = prior.get(str(p))
            if old and (str(p).startswith(str(PACKAGES) + '/') or str(p) in advice.TOOL_ADVICE):
                spec.update(expected_sha256=old['sha256'], expected_identity=old['identity'])
                if advice.eligible(p) and not p.stat().st_mode & 0o111:
                    spec['advice_scope'] = 'reviewed_dependency_or_tool_object'
            specs[p] = spec
        for row in self.graph:
            specs[R / row['path']]['expected_sha256'] = row['sha256']
        specs[B / 'PLAN.json']['expected_sha256'] = PLAN_SHA
        specs[R / 'checkpoints/light-eft-batch50-entries22-71-20261017/inputs.jsonl']['expected_sha256'] = '6a366f1acfa3f8824ce90a210ba55e3d28ac0cac8a70fff1ac1e41a5fbb1b4bd'
        for p, value in [(LEAN, 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'),
                         (CHECKER, 'ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'),
                         (RESOLVER, '9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf'),
                         (R / PLAN['source_graph_path'], PLAN['source_graph_sha256']),
                         (R / PLAN['recovery_scope_reference'], PLAN['recovery_scope_sha256'])]:
            specs[p]['expected_sha256'] = value
        for x in PLAN['accepted_seeds']:
            specs[R / x['path']]['expected_sha256'] = x['sha256']
        for x in PLAN['accepted_seed_evidence']:
            specs[R / x['path']]['expected_sha256'] = x['sha256']
        specs[R / 'lake-manifest.json']['expected_sha256'] = '615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f'
        specs[R / 'lean-toolchain']['expected_sha256'] = '8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632'
        recovery = [json.loads(x) for x in (R / PLAN['recovery_scope_reference']).read_text().splitlines()]
        selected = [x for x in recovery if x['status'] == 'advised']
        if len(selected) != 7129 or sum(x['bytes'] for x in selected) != 3078727377:
            raise RuntimeError('Previously accepted data advice scope mismatch')
        for row in selected:
            p = R / row['path']
            if p not in execution:
                specs[p] = {'role': 'preserved_advice_data', 'expected_sha256': row['sha256'],
                            'expected_identity': row['identity_after_advice'], 'advice_scope': 'previously_accepted_evidence_data'}
        del prior
        for authority in PLAN['expanded_advice_manifests'] + PLAN['new_archive_authorities'] + PLAN['new_data_manifests']:
            specs[R / authority['path']]['expected_sha256'] = authority['sha256']
        for name, row in self.expanded_rows.items():
            target = Path(name)
            previous = specs.get(target, {})
            if previous.get('expected_sha256', row['sha256']) != row['sha256']:
                raise RuntimeError('Expanded scope conflicts with existing pin')
            if previous.get('expected_identity') and row.get('expected_identity') and previous['expected_identity'] != row['expected_identity']:
                raise RuntimeError('New advice scope conflicts with an existing identity pin')
            specs[target] = {**previous, 'role': 'reviewed_finalized_data', 'expected_sha256': row['sha256'], 'expected_bytes': row['bytes'], 'advice_scope': row['scope'], **({'expected_identity': row['expected_identity']} if 'expected_identity' in row else {})}
        self.frozen = FrozenInputs(specs, B)
        self.frozen.lock = self.lock
        self.input_ref = self.frozen.freeze()
        (B / 'input-inventory-reference.json').write_text(json.dumps(self.input_ref, indent=2) + '\n')
        self.small = [p for p in execution if p in set(B.glob('*.py')) or p == RESOLVER or p == R / 'scripts/LightEFTProcessLifecycle.py' or p == B / 'PLAN.json']
        self.harness_digest = hashlib.sha256(b''.join(encode(self.frozen.rows[str(p)]) for p in sorted(self.small))).hexdigest()

    def membership(self):
        if self.project_sources() != self.source_membership or self.execution_paths() != self.execution_membership:
            raise RuntimeError('Frozen input/search membership changed')
        self.check_pins()

    def source(self, plan):
        return RESOLVER if plan['stage'] == 'resolve' else R / self.modules[plan['module']]['path']

    def resolution_path(self, module):
        return WORK / 'resolutions' / (module + '.json')

    def object_path(self, module):
        return OUT / Path(*module.split('.')).with_suffix('.olean')

    def environment(self, module, stage):
        env = {'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'LEAN_SYSROOT': str(TOOL),
               'LEAN_PATH': os.pathsep.join(map(str, [OUT] + self.roots)),
               'LEAN_SRC_PATH': os.pathsep.join(map(str, self.project_roots + [PACKAGES / p['name'] for p in self.pins] + [TOOL / 'src/lean'])),
               'MIMALLOC_ARENA_RESERVE': '128MiB'}
        if stage == 'compile':
            env['MIMALLOC_VERBOSE'] = '1'
        elif stage == 'resolve':
            env.update(LIGHTEFT_CHECKER_TARGET=module, LIGHTEFT_CHECKER_RESOLUTION_FILE=str(self.resolution_path(module)))
        elif stage == 'replay':
            env.update(LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='65536')
        else:
            raise RuntimeError('Unauthorized stage')
        return env

    def argv(self, module, stage):
        if module == 'LightEFTSpanners' and stage != 'compile':
            raise RuntimeError('Aggregate permits compilation only; resolver and prefix replay remain forbidden')
        if module not in self.modules or stage not in self.modules[module]['remaining_stages']:
            raise RuntimeError('Stage absent from the exact 343-stage finite batch; accepted compile/resolution cannot rerun')
        if module == 'LightSpanners.RetainedGraph' and stage != 'replay':
            raise RuntimeError('RetainedGraph compilation/resolution must not be repeated')
        if stage=='compile' and module in {x['module'] for x in PLAN['accepted_seeds']}:
            raise RuntimeError('Recompilation of accepted seed forbidden')
        flags = ['-j1', '-s65536', '-M5120', '-DautoImplicit=false', '-DwarningAsError=true']
        if stage == 'compile':
            row = self.modules[module]
            return [str(LEAN), *flags, '--root=' + str(R / row['srcDir']), '-o', str(self.object_path(module)), str(R / row['path'])]
        if stage == 'resolve':
            return [str(LEAN), *flags, str(RESOLVER)]
        if stage == 'replay':
            return [str(CHECKER), '-v', module]
        raise RuntimeError('Unauthorized stage')

    def visible_gate(self, plan):
        return 4294967296 if plan['stage'] == 'replay' else 3221225472

    def check_objects(self, plan=None, allow_new=False):
        for name, row in (self.resolutions | self.partial_resolutions).items():
            if inspect(name, {'role': row['role']}) != row:
                raise RuntimeError('Accepted generated resolution changed: ' + name)
        actual = {str(p): p for p in OUT.rglob('*') if p.is_file()}
        for name, row in self.ledger.items():
            if name not in actual or inspect(name, {'role': 'project_object'}) != row:
                raise RuntimeError('Previously built project object changed: ' + name)
        new = set(actual) - set(self.ledger)
        if self.partial_outputs:
            for name, row in self.partial_outputs.items():
                if name not in actual or inspect(name, {'role': 'project_object'}) != row:
                    raise RuntimeError('Preserved failed output changed: ' + name)
            new -= set(self.partial_outputs)
        if new:
            target = str(self.object_path(plan['module'])) if plan else ''
            permitted = {target, target + '.private', target + '.server', str(Path(target).with_suffix('.ilean')), str(Path(target).with_suffix('.ir'))}
            if not allow_new or not new <= permitted:
                raise RuntimeError('Unexpected output membership: ' + repr(sorted(new)))
        return {name: inspect(actual[name], {'role': 'project_object'}) for name in sorted(new)}

    def check_work_membership(self, allowed_resolution=None):
        expected = {str(p) for p in OUT.rglob('*') if p.is_file()} | set(self.resolutions) | set(self.partial_resolutions)
        if allowed_resolution is not None:
            expected.add(str(allowed_resolution))
        observed = {str(p) for p in WORK.rglob('*') if p.is_file()}
        if observed - expected:
            raise RuntimeError('Unexpected work-directory membership: ' + repr(sorted(observed - expected)))

    def verify_resolution(self, module):
        p = self.resolution_path(module)
        data = json.loads(p.read_text())
        if data['target'] != module or data['count'] != 1 or data['resolved'] != [{'module': module, 'object': str(self.object_path(module))}]:
            raise RuntimeError('Official target resolution is not exact singleton/new object')
        found = []
        for root in [OUT] + self.roots:
            for p in root.rglob('*.olean'):
                name = '.'.join(p.relative_to(root).with_suffix('').parts)
                if name == module or name.startswith(module + '.'):
                    found.append((name, str(p)))
        if found != [(module, str(self.object_path(module)))]:
            raise RuntimeError('Missing/shadowed/prefix-expanded checker target')
        return data

    def before_child(self, plan, record, save):
        record['stage_kind'] = 'aggregate_compile' if self.modules[plan['module']]['aggregate'] else plan['stage']
        record.update(module=plan['module'], canonical_input_inventory=self.input_ref,
                      harness_sha256=self.harness_digest, final_full_content_verification_required=True,
                      output_ledger_version=self.ledger_version)
        if plan['module'] not in self.modules or plan['argv'] != self.argv(plan['module'], plan['stage']) or plan['env'] != self.environment(plan['module'], plan['stage']):
            raise RuntimeError('Not the exact finite authorized module/stage')
        self.frozen.identities()
        self.membership()
        source = self.source(plan)
        for p in self.small + [source]:
            row = inspect(p, self.frozen.specs[str(p)])
            if row != self.frozen.rows[str(p)]:
                raise RuntimeError('Small submitted source/harness hash changed')
        self.check_objects()
        self.check_work_membership()
        if plan['stage'] == 'resolve' and self.resolution_path(plan['module']).exists():
            raise RuntimeError('Resolution path is not fresh')
        if plan['stage'] == 'replay':
            data = self.verify_resolution(plan['module'])
            record['official_resolution'] = data
        path = B / 'sources' / (digest(source) + '.lean.txt')
        path.parent.mkdir(exist_ok=True)
        if not path.exists():
            path.write_bytes(source.read_bytes())
        record.update(submitted_source_sha256=digest(source), source_snapshot=str(path.relative_to(B)),
                      between_child_preservation_passed=True)
        save()

    def prepare_child(self, plan, record, save, accounting):
        label = plan['module'] + ':' + plan['stage']
        child.assert_idle(label, record)
        initial = accounting.sample()
        first_planned = {'module': plan['module'], 'stage': plan['stage']} == PLAN['first_planned_stage']
        if first_planned or initial['headroom'] < self.visible_gate(plan):
            info = self.frozen.advise_once_extension(accounting, label) if first_planned else self.frozen.advise_verified(accounting, label)
            for a, b in zip(info['before']['nodes'], info['after']['nodes'], strict=True):
                if a['oom'] != b['oom'] or a['pids_events'] != b['pids_events']:
                    raise child.MemoryGuardError('OOM/PID event changed in idle interval')
            advice_ref = {'label': label, 'scope_identity_sha256': info['scope_identity_sha256'], 'counts': info['counts'], 'bytes': info['bytes']}
        else:
            advice_ref = {'label': label, 'state': 'not_needed_actual_capacity_sufficient', 'initial_visible_bytes': initial['headroom']}
        now = accounting.sample()
        record.update(admission=now, idle_advice_reference=advice_ref)
        save()
        child.check_memory(now, now, self.visible_gate(plan))
        if now['system_available'] < 3221225472:
            raise child.MemoryGuardError('Host MemAvailable below admission floor')
        if shutil.disk_usage(WORK).free <= 2 * 1024**3:
            raise RuntimeError('Insufficient disk')
        return now

    def after_child(self, plan, record, save):
        self.frozen.identities()
        self.membership()
        for p in self.small + [self.source(plan)]:
            if inspect(p, self.frozen.specs[str(p)]) != self.frozen.rows[str(p)]:
                raise RuntimeError('Small source/harness changed after child')
        new = self.check_objects(plan, allow_new=plan['stage'] == 'compile')
        self.check_work_membership(self.resolution_path(plan['module']) if plan['stage'] == 'resolve' else None)
        if plan['stage'] == 'compile' and record.get('exit') == 0 and 'failure' not in record:
            if str(self.object_path(plan['module'])) not in new:
                raise RuntimeError('Successful compiler produced no fresh target object')
            self.ledger.update(new)
            record['output_delta'] = list(new.values())
            self.save_ledger(plan['module'])
        elif new:
            self.partial_outputs.update(new)
            record['failed_output_delta'] = list(new.values())
        if plan['stage'] == 'resolve' and record.get('exit') == 0 and 'failure' not in record:
            record['official_resolution'] = self.verify_resolution(plan['module'])
            p = self.resolution_path(plan['module'])
            self.resolutions[str(p)] = inspect(p, {'role': 'resolution_record'})
            record['resolution_binding'] = self.resolutions[str(p)]
        elif plan['stage'] == 'resolve' and self.resolution_path(plan['module']).exists():
            p = self.resolution_path(plan['module'])
            self.partial_resolutions[str(p)] = inspect(p, {'role': 'failed_resolution_record'})
            record['failed_resolution_binding'] = self.partial_resolutions[str(p)]
        record['between_child_preservation_passed'] = True
        save()

    def save_ledger(self, label):
        self.ledger_version += 1
        with (B / 'output-records.jsonl').open('a') as f:
            f.write(json.dumps({'version': self.ledger_version, 'label': label, 'utc': utc(), 'objects': list(self.ledger.values())}, separators=(',', ':')) + '\n')
            f.flush()
            os.fsync(f.fileno())

    def output_summary(self):
        data = b''.join(encode(x) for x in self.ledger.values())
        return {'ledger_version': self.ledger_version, 'files': len(self.ledger), 'sha256': hashlib.sha256(data).hexdigest()}

    def complete_log(self, path, record, save):
        with path.open('r+b') as f:
            f.flush()
            os.fsync(f.fileno())
            a = os.fstat(f.fileno())
            value = hashlib.file_digest(f, 'sha256').hexdigest()
            b = os.fstat(f.fileno())
            if signature(a) != signature(b):
                raise RuntimeError('Completed child log changed')
            os.posix_fadvise(f.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
            if signature(os.fstat(f.fileno())) != signature(b):
                raise RuntimeError('Completed child log changed during advice')
        record.setdefault('completed_logs', {})[path.name] = {'sha256': value, 'bytes': b.st_size, 'identity': signature(b), 'fsynced_advised': True}
        save()

    def final_verify(self):
        result = self.frozen.final_verify()
        try:
            self.membership()
            self.check_objects()
            self.check_work_membership()
        except Exception as exc:
            result['matching'] = False
            result['membership_or_output_error'] = repr(exc)
        if self.preservation_failed:
            result['matching'] = False
            result['prior_preservation_failure'] = True
        (B / 'final-content-verification.json').write_text(json.dumps(result, indent=2) + '\n')
        return result
