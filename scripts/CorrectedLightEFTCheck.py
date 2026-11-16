#!/usr/bin/env python3
"""Source-bound, memory-bounded validation of the corrected Light EFT library.

Run from the repository root with the pinned toolchain and mathlib installed.
This is a verification harness, not a mathematical premise.  No network,
publication, historical-checkpoint policy, or approval gate is involved.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import tomllib


def sha(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def load_json(path: Path, default):
    if not path.exists():
        return default
    # The adopted in-session builder updates its JSON file in place.
    for attempt in range(5):
        try:
            return json.loads(path.read_text())
        except json.JSONDecodeError:
            if attempt == 4:
                raise
            time.sleep(0.02 * (attempt + 1))


def uncomment(text: str) -> str:
    """Remove nested Lean comments while preserving line boundaries."""
    out, index, depth = [], 0, 0
    while index < len(text):
        if text.startswith('/-', index):
            depth += 1
            out.append('  ')
            index += 2
        elif depth and text.startswith('-/', index):
            depth -= 1
            out.append('  ')
            index += 2
        elif depth:
            out.append('\n' if text[index] == '\n' else ' ')
            index += 1
        elif text.startswith('--', index):
            end = text.find('\n', index)
            if end == -1:
                break
            out.append('\n')
            index = end + 1
        else:
            out.append(text[index])
            index += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(out)


def imports(path: Path) -> list[str]:
    result = []
    for line in uncomment(path.read_text()).splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*', line)
        if match:
            names = match.group(1).split()
            if not all(re.fullmatch(r'[\w]+(?:\.[\w]+)*', name) for name in names):
                raise ValueError(f'Unsupported import syntax in {path}: {line}')
            result.extend(names)
    return result


class Checker:
    def __init__(self, options):
        self.args = options
        self.root = options.root.resolve()
        self.state = options.state.resolve()
        self.state.mkdir(parents=True, exist_ok=True)
        self.scripts = Path(__file__).resolve().parent
        self.harness_hash = sha(Path(__file__).resolve())
        self.env = dict(os.environ)
        self.env['LEAN_NUM_THREADS'] = '1'
        self.env.pop('LEAN_OPTS', None)
        self.env.pop('LEAN_OPTIONS', None)
        self.capture = lambda args: subprocess.check_output(args, cwd=self.root, env=self.env, text=True).strip()
        self.sysroot = Path(self.capture(['lake', 'env', 'lean', '--print-prefix'])).resolve()
        self.lean = self.sysroot / 'bin/lean'
        self.checker = self.sysroot / 'bin/leanchecker'
        self.search = []
        for item in self.capture(['lake', 'env', 'printenv', 'LEAN_PATH']).split(os.pathsep):
            if item:
                path = Path(item)
                path = (self.root / path).resolve() if not path.is_absolute() else path.resolve()
                if path not in self.search:
                    self.search.append(path)
        if self.sysroot / 'lib/lean' not in self.search:
            self.search.append(self.sysroot / 'lib/lean')
        self.env['LEAN_PATH'] = os.pathsep.join(map(str, self.search))
        self.env['LEAN_SYSROOT'] = str(self.sysroot)
        self.env['LEAN_SRC_PATH'] = str(self.root)
        self.version = self.capture([str(self.lean), '--version'])
        pin = (self.root / 'lean-toolchain').read_text().strip()
        if pin != 'leanprover/lean4:v4.34.0' or 'version 4.34.0' not in self.version:
            raise ValueError('Unexpected Lean toolchain: ' + self.version)
        if '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b' not in self.version:
            raise ValueError('Unexpected official Lean release commit')
        configuration = tomllib.loads((self.root / 'lakefile.toml').read_text())
        self.aggregate_modules = {lib['name'] for lib in configuration['lean_lib']}
        self.modules = {}
        for library in configuration['lean_lib']:
            base = Path(library.get('srcDir', '.'))
            stem = Path(*library['name'].split('.'))
            candidates = [self.root / base / stem.with_suffix('.lean')]
            directory = self.root / base / stem
            if directory.is_dir():
                candidates.extend(directory.rglob('*.lean'))
            for path in candidates:
                if path.is_file():
                    name = '.'.join(path.relative_to(self.root / base).with_suffix('').parts)
                    item = {'path': path, 'source_root': base, 'imports': imports(path)}
                    if name in self.modules and self.modules[name] != item:
                        raise ValueError('Ambiguous project module ' + name)
                    self.modules[name] = item
        self.order, seen, active = [], set(), set()
        def visit(name):
            if name in seen:
                return
            if name in active:
                raise ValueError('Project import cycle ' + name)
            if name not in self.modules:
                raise ValueError('Missing aggregate module ' + name)
            active.add(name)
            for child in self.modules[name]['imports']:
                if child in self.modules:
                    visit(child)
                elif child.startswith(('LightEFTSpanners.', 'LightSpanners.', 'CorrectedLightEFTSpanners')):
                    raise ValueError('Unmapped project import ' + child)
            active.remove(name)
            seen.add(name)
            self.order.append(name)
        visit(options.target)
        if options.target == 'CorrectedLightEFTSpanners':
            missing = {n for n in self.modules if n.startswith('LightEFTSpanners.')} - seen
            if missing:
                raise ValueError('Corrected aggregate omits paper source modules: ' + repr(sorted(missing)))
        self.initial_sources = {name: sha(self.modules[name]['path']) for name in self.order}
        self.initial_controls = {name: sha(self.root / name) for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']}
        self.identity = {
            'lean_version': self.version, 'sysroot': str(self.sysroot),
            'lean_sha256': sha(self.lean), 'leanchecker_sha256': sha(self.checker),
            'leanchecker_source_sha256': sha(self.sysroot / 'src/lean/LeanChecker.lean'),
            'controls': self.initial_controls,
            'dependencies': self.dependency_pins(),
        }
        compiler_identity = dict(self.identity)
        # Direct lean calls use explicit flags and search paths. Adding a new
        # lake_lib does not change this compiler or an existing object's inputs.
        compiler_identity['controls'] = {key: value for key, value in self.initial_controls.items() if key != 'lakefile.toml'}
        canonical_identity = json.dumps(compiler_identity, sort_keys=True)
        (self.state / 'compiler-identity.json').write_text(canonical_identity)
        self.identity_hash = hashlib.sha256(canonical_identity.encode()).hexdigest()
        self.external_cache = {}
        self.records = load_json(self.state / 'compile-manifest.json', {})
        self.replays = load_json(self.state / 'replay-manifest.json', {})
        self.baseline = load_json(options.baseline, {}) if options.baseline else {}
        if options.baseline:
            write_json(self.state / 'baseline-source-build.json', self.baseline)
            builder = options.baseline.parent.parent / 'build_sequential.py'
            write_json(self.state / 'baseline-provenance.json', {
                'manifest': str(options.baseline),
                'manifest_sha256': sha(options.baseline),
                'snapshot_sha256': sha(self.state / 'baseline-source-build.json'),
                'builder_sha256': sha(builder) if builder.exists() else None,
                'scope': 'in-session source-bound strict compilation; independently singleton-replayed',
                'not_an_empty_tree_rebuild': True})
        write_json(self.state / 'toolchain-identity.json', self.identity)
        write_json(self.state / 'source-graph.json', [{
            'module': name, 'source': str(self.modules[name]['path'].relative_to(self.root)),
            'source_sha256': self.initial_sources[name], 'imports': self.modules[name]['imports'],
        } for name in self.order])
        (self.state / 'project-modules.txt').write_text('\n'.join(self.order) + '\n')
        self.lock = options.lock.resolve()
        self.lock.parent.mkdir(parents=True, exist_ok=True)

    def dependency_pins(self):
        result = []
        for entry in json.loads((self.root / 'lake-manifest.json').read_text())['packages']:
            directory = self.root / '.lake/packages' / entry['name']
            actual = self.capture(['git', '-C', str(directory), 'rev-parse', 'HEAD'])
            if actual != entry['rev']:
                raise ValueError('Dependency revision mismatch: ' + entry['name'])
            dirty = self.capture(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'])
            if dirty:
                raise ValueError('Modified dependency source: ' + entry['name'])
            result.append({'name': entry['name'], 'revision': actual, 'url': entry.get('url')})
        return result

    def artifact(self, name):
        rel = Path(*name.split('.')).with_suffix('.olean')
        found = [base / rel for base in self.search if (base / rel).is_file()]
        resolved = list(dict.fromkeys(path.resolve() for path in found))
        if len(resolved) != 1:
            raise ValueError(f'Missing or shadowed object {name}: {resolved}')
        return resolved[0]

    def artifact_hashes(self, name):
        path = self.artifact(name)
        result = {'olean': sha(path)}
        for suffix in ['.olean.server', '.olean.private']:
            candidate = path.with_suffix(suffix)
            if candidate.exists():
                result[suffix[1:]] = sha(candidate)
        return result

    def external_binding(self, name):
        if name not in self.external_cache:
            self.external_cache[name] = self.artifact_hashes(name)
        return self.external_cache[name]

    def binding(self, name):
        project, external = {}, {}
        for child in self.modules[name]['imports']:
            if child in self.modules:
                project[child] = self.artifact_hashes(child)
            else:
                external[child] = self.external_binding(child)
        return {
            'source_sha256': sha(self.modules[name]['path']),
            'project_dependencies': project, 'external_dependencies': external,
            'toolchain_identity_sha256': self.identity_hash,
            'source_root': str(self.modules[name]['source_root']),
        }

    def unchanged(self):
        for name, expected in self.external_cache.items():
            if self.artifact_hashes(name) != expected:
                raise ValueError('Dependency object changed during validation: ' + name)
        if sha(self.lean) != self.identity['lean_sha256'] or sha(self.checker) != self.identity['leanchecker_sha256']:
            raise ValueError('Compiler binary changed during validation')
        for name, expected in self.initial_sources.items():
            if sha(self.modules[name]['path']) != expected:
                raise ValueError('Source changed during validation: ' + name)
        for name, expected in self.initial_controls.items():
            if sha(self.root / name) != expected:
                raise ValueError('Build control changed during validation: ' + name)

    @contextlib.contextmanager
    def locked(self):
        with self.lock.open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            yield lock
        # Let waiting mathematical proof compilers advance between modules.
        time.sleep(0.05)

    def run(self, label, command, env=None, extra=None):
        attempt = self.state / 'attempts' / (str(time.time_ns()) + '-' + label)
        attempt.mkdir(parents=True)
        record = {'label': label, 'argv': command, 'cwd': str(self.root),
                  'toolchain_identity_sha256': self.identity_hash,
                  'started_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
                  'start_monotonic_ns': time.monotonic_ns(),
                  'harness_sha256': self.harness_hash, **(extra or {})}
        write_json(attempt / 'receipt.json', record)
        child = None
        try:
            with (attempt / 'output.log').open('w') as log:
                child = subprocess.Popen(command, cwd=self.root, env=env or self.env,
                                         stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                record['pid'] = child.pid
                write_json(attempt / 'receipt.json', record)
                record['exit_code'] = child.wait()
            if record['exit_code']:
                raise RuntimeError(f'{label} exited {record["exit_code"]}: {attempt / "output.log"}\n' +
                                   (attempt / 'output.log').read_text()[-5000:])
            return (attempt / 'output.log').read_text(), attempt
        finally:
            if child is not None and child.poll() is None:
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            if child is not None:
                record['exit_code'] = child.returncode
            record.update(end_monotonic_ns=time.monotonic_ns(),
                          child_reaped=child is not None and child.poll() is not None)
            record['log_sha256'] = sha(attempt / 'output.log') if (attempt / 'output.log').exists() else None
            write_json(attempt / 'receipt.json', record)

    def adopt_baseline(self, name, binding):
        old = self.baseline.get(name)
        if not old or not old.get('strict') or old.get('source_sha256') != binding['source_sha256']:
            return None
        expected = {child: parts['olean'] for child, parts in binding['project_dependencies'].items()}
        if old.get('dependencies') != expected:
            return None
        try:
            hashes = self.artifact_hashes(name)
        except ValueError:
            return None
        if old.get('artifact_sha256') != hashes['olean']:
            return None
        # Explicit provenance: this is this session's source-bound sequential
        # build, not a claim to have rerun that compilation from an empty tree.
        return {**binding, 'artifacts': hashes, 'source': str(self.modules[name]['path'].relative_to(self.root)),
                'strict': True, 'origin': 'in-session-source-bound-baseline',
                'baseline_manifest': str(self.args.baseline),
                'baseline_record_sha256': hashlib.sha256(json.dumps(old, sort_keys=True).encode()).hexdigest(),
                'baseline_seconds': old.get('seconds'),
                'adoption_compiler_identity': self.identity_hash}

    def ready(self, name):
        try:
            binding = self.binding(name)
            hashes = self.artifact_hashes(name)
        except ValueError:
            return None
        old = self.records.get(name)
        if old and all(old.get(k) == value for k, value in binding.items()) and old.get('artifacts') == hashes:
            return old
        adopted = self.adopt_baseline(name, binding)
        if adopted:
            self.records[name] = adopted
            write_json(self.state / 'compile-manifest.json', self.records)
        return adopted

    def compile(self):
        for index, name in enumerate(self.order, 1):
            with self.locked():
                if self.ready(name):
                    continue
                binding = self.binding(name)
                item = self.modules[name]
                output = self.root / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')
                output.parent.mkdir(parents=True, exist_ok=True)
                command = [str(self.lean), '-j1', '-M' + str(self.args.memory_mb),
                           '-DautoImplicit=false', '-DwarningAsError=true',
                           '-R', str(item['source_root']), '-o', str(output),
                           '-i', str(output.with_suffix('.ilean')), str(item['path'].relative_to(self.root))]
                raw, attempt = self.run('compile-' + name, command, extra={'binding': binding})
                if re.search(r'^.*:\d+:\d+: warning:', raw, re.M):
                    raise ValueError('Warning in strict compilation ' + name)
                if self.binding(name) != binding:
                    raise ValueError('Inputs changed during compilation ' + name)
                self.records[name] = {**binding, 'artifacts': self.artifact_hashes(name),
                    'source': str(item['path'].relative_to(self.root)), 'strict': True,
                    'origin': 'strict-compiler-invocation', 'attempt': str(attempt.relative_to(self.state))}
                write_json(self.state / 'compile-manifest.json', self.records)
            if index % 20 == 0 or index == len(self.order):
                print(f'COMPILE {index}/{len(self.order)} {name}', flush=True)
        self.unchanged()

    def singleton(self, name):
        if any(other.startswith(name + '.') for other in self.modules):
            raise ValueError('Prefix aggregate is not a singleton checker target: ' + name)
        selected = {}
        stem = Path(*name.split('.'))
        for base in self.search:
            exact = base / stem.with_suffix('.olean')
            if exact.exists():
                selected.setdefault(name, set()).add(str(exact.resolve()))
            directory = base / stem
            if directory.is_dir():
                for path in directory.rglob('*.olean'):
                    child = '.'.join(path.relative_to(base).with_suffix('').parts)
                    selected.setdefault(child, set()).add(str(path.resolve()))
        normalized = {key: sorted(value) for key, value in selected.items()}
        if set(normalized) != {name} or len(normalized[name]) != 1:
            raise ValueError('Non-singleton checker resolution: ' + repr(normalized))
        return {'target': name, 'count': 1, 'resolved': normalized,
                'selection_semantics': 'pinned LeanChecker.lean target.isPrefixOf module',
                'search_path': list(map(str, self.search))}

    def replay_targets(self):
        targets = []
        for name in self.order:
            aggregate = name in self.aggregate_modules or any(other.startswith(name + '.') for other in self.modules)
            if aggregate:
                lines = [line.strip() for line in uncomment(self.modules[name]['path'].read_text()).splitlines() if line.strip()]
                if not all(re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+.+', line) for line in lines):
                    raise ValueError('Cannot omit declarations in a prefix/aggregate module from kernel replay: ' + name)
            else:
                targets.append(name)
        return targets

    def replay(self):
        targets = self.replay_targets()
        for index, name in enumerate(targets, 1):
            with self.locked():
                ready = self.ready(name)
                if not ready:
                    if self.args.available_only:
                        continue
                    raise ValueError('Missing source-bound compilation for replay: ' + name)
                binding = self.binding(name)
                hashes = self.artifact_hashes(name)
                old = self.replays.get(name, {})
                if old.get('binding') == binding and old.get('artifacts') == hashes and old.get('exit_code') == 0:
                    continue
                resolution = self.singleton(name)
                raw, attempt = self.run('replay-' + name,
                    [str(self.checker), '-v', name],
                    extra={'binding': binding, 'artifacts': hashes, 'resolution': resolution})
                if raw.strip() != 'replaying ' + name:
                    raise ValueError('Official checker did not replay exactly one expected target: ' + repr(raw))
                if self.binding(name) != binding or self.artifact_hashes(name) != hashes:
                    raise ValueError('Inputs changed during replay: ' + name)
                self.replays[name] = {'binding': binding, 'artifacts': hashes, 'exit_code': 0,
                                     'attempt': str(attempt.relative_to(self.state)), 'resolution': resolution}
                write_json(self.state / 'replay-manifest.json', self.replays)
            if index % 20 == 0 or index == len(targets):
                print(f'REPLAY {index}/{len(targets)} {name}', flush=True)
        self.unchanged()

    def audit(self):
        for name in self.order:
            if not self.ready(name):
                raise ValueError('Missing source-bound compilation for audit: ' + name)
        env = dict(self.env)
        output = self.state / 'audit'
        env['CORRECTED_LIGHT_EFT_MODULES'] = str(self.state / 'project-modules.txt')
        env['CORRECTED_LIGHT_EFT_AUDIT_OUTPUT'] = str(output)
        audit = self.scripts / 'CorrectedLightEFTAudit.lean'
        with self.locked():
            raw, attempt = self.run('all-actual-owner-audit',
                [str(self.lean), '-j1', '-M' + str(self.args.memory_mb),
                 '-DautoImplicit=false', '-DwarningAsError=true', str(audit)], env=env,
                extra={'audit_source_sha256': sha(audit),
                       'source_graph_sha256': sha(self.state / 'source-graph.json')})
        summary = load_json(output / 'summary.json', {})
        if summary.get('findings') != 0 or (output / 'strict-violations.txt').read_text():
            raise ValueError('Strict declaration audit failed')
        # Bind all actually loaded dependency objects, not only direct imports.
        loaded = (output / 'import-closure-loaded.txt').read_text().splitlines()
        dependencies = {name: self.artifact_hashes(name) for name in loaded if name not in self.modules}
        write_json(self.state / 'loaded-dependency-artifacts.json', dependencies)
        write_json(self.state / 'audit-receipt.json', {'attempt': str(attempt.relative_to(self.state)),
                   'source_graph_sha256': sha(self.state / 'source-graph.json'),
                   'audit_source_sha256': sha(audit),
                   'loaded_dependencies_sha256': sha(self.state / 'loaded-dependency-artifacts.json'),
                   'project_artifacts': {name: self.artifact_hashes(name) for name in self.order},
                   'summary': summary})
        self.unchanged()
        print('AUDIT ' + json.dumps(summary, sort_keys=True), flush=True)

    def finish(self):
        self.unchanged()
        compile_complete = all(self.ready(name) for name in self.order)
        targets = self.replay_targets()
        replay_complete = all(name in self.replays and self.replays[name].get('binding') == self.binding(name)
                              and self.replays[name].get('artifacts') == self.artifact_hashes(name)
                              and self.replays[name].get('exit_code') == 0 for name in targets) if compile_complete else False
        audit = load_json(self.state / 'audit-receipt.json', {})
        audit_complete = (audit.get('source_graph_sha256') == sha(self.state / 'source-graph.json')
                          and audit.get('summary', {}).get('findings') == 0
                          and audit.get('audit_source_sha256') == sha(self.scripts / 'CorrectedLightEFTAudit.lean')
                          and audit.get('project_artifacts') == {name: self.artifact_hashes(name) for name in self.order}) if compile_complete else False
        status = 'PASS' if compile_complete and replay_complete and audit_complete else 'INCOMPLETE'
        result = {'status': status, 'target': self.args.target, 'project_modules': len(self.order),
                  'singleton_targets': len(targets), 'valid_compilations': sum(bool(self.ready(n)) for n in self.order),
                  'valid_replays': sum(n in self.replays and self.ready(n) is not None
                                      and self.replays[n].get('binding') == self.binding(n)
                                      and self.replays[n].get('artifacts') == self.artifact_hashes(n)
                                      and self.replays[n].get('exit_code') == 0 for n in targets),
                  'compile_complete': compile_complete, 'replay_complete': replay_complete,
                  'audit_complete': audit_complete, 'source_graph_sha256': sha(self.state / 'source-graph.json'),
                  'toolchain_identity_sha256': self.identity_hash,
                  'baseline_adoption_is_not_empty_tree_rebuild': bool(self.args.baseline),
                  'harness_sha256': self.harness_hash,
                  'audit_source_sha256': sha(self.scripts / 'CorrectedLightEFTAudit.lean')}
        write_json(self.state / 'result.json', result)
        print(json.dumps(result, sort_keys=True), flush=True)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--target', default='CorrectedLightEFTSpanners')
    parser.add_argument('--phase', choices=['inventory', 'compile', 'replay', 'audit', 'all'], default='all')
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--available-only', action='store_true')
    parser.add_argument('--lock', type=Path, default=Path('/workspace/formalization/new-lean.lock'))
    parser.add_argument('--memory-mb', type=int, default=6000)
    options = parser.parse_args()
    if sys.flags.optimize:
        raise SystemExit('Run without Python optimization')
    checker = Checker(options)
    previous_failure = checker.state / 'failure.json'
    if previous_failure.exists():
        history = checker.state / 'history'
        history.mkdir(exist_ok=True)
        previous_failure.replace(history / ('failure-' + str(time.time_ns()) + '.json'))
    write_json(checker.state / 'result.json', {'status': 'RUNNING', 'target': options.target,
               'phase': options.phase, 'source_graph_sha256': sha(checker.state / 'source-graph.json')})
    print(json.dumps({'target': options.target, 'modules': len(checker.order),
                      'phase': options.phase, 'threads': 1, 'memory_mb': options.memory_mb}), flush=True)
    try:
        if options.phase in ['compile', 'all']:
            checker.compile()
        if options.phase in ['replay', 'all']:
            checker.replay()
        if options.phase in ['audit', 'all']:
            checker.audit()
        checker.finish()
    except BaseException as error:
        write_json(checker.state / 'failure.json', {'error': repr(error),
                   'target': options.target, 'phase': options.phase})
        write_json(checker.state / 'result.json', {'status': 'FAILED', 'error': repr(error)})
        raise


if __name__ == '__main__':
    main()
