#!/usr/bin/env python3
"""Source-only preflight by default. --execute requires an explicitly pinned commit.

No inherited source/gate is edited. Execution is not acceptance: independent
post-execution review and the complete exact-commit CI evidence remain required.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PAPER = 'Improved Upper Bounds for the Directed Flow-Cut Gap'
REQUIRED = [
    'DirectedFlowCutGap.OriginalStoreCorrectness.' + x for x in
    ['CorrectForInput', 'correct_not_invalid', 'solve_original_correct_bit',
     'solve_original_correct_polynomial_bit']]


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, timeout=30)


def validator_snapshot():
    files = {p for p in HERE.rglob('*') if p.is_file()}
    files.add(REPO / '.github/workflows/flow-737-validation.yml')
    return {str(p.relative_to(REPO)): digest(p.read_bytes()) for p in sorted(files)}


def postflight_identity(report, expected_commit, source, output):
    """Common fail-closed final identity check, including after failed attempts."""
    errors = {}
    def check(field, action):
        try:
            report[field] = bool(action())
        except Exception as exc:
            report[field] = False
            errors[field] = str(exc)
    check('head_postflight_passed',
          lambda: git('rev-parse', 'HEAD').decode().strip() == expected_commit)
    check('validator_postflight_passed',
          lambda: validator_snapshot() == report['validator_bindings'])
    def overlay_matches():
        root = output / 'src'
        expected = {n.replace('.', '/') + '.lean': digest(data) for n, data in source.items()}
        actual = {str(p.relative_to(root)): digest(p.read_bytes())
                  for p in root.rglob('*') if p.is_file()}
        return actual == expected
    check('overlay_postflight_passed', overlay_matches)
    if errors:
        report['identity_postflight_errors'] = errors
    passed = all(report[k] for k in ['head_postflight_passed',
                 'validator_postflight_passed', 'overlay_postflight_passed'])
    if not passed:
        report['status'] = 'failed'
    return passed


def blob(entry):
    data = git('show', entry['commit'] + ':' + entry['repository_path'])
    need(digest(data) == entry['sha256'], 'Source binding mismatch: ' + entry['repository_path'])
    return data


def imports(data):
    return [n for line in data.decode().splitlines() if line.startswith('import ')
            for n in line[7:].split() if n.startswith('DirectedFlowCutGap.')]


def plan():
    m = json.loads((HERE / 'MODULES.json').read_text())
    modules = m['modules']
    base = {n for n, e in modules.items() if e['kind'] == 'baseline'}
    new = set(modules) - base
    reference = json.loads(git('show', m['baseline'] + ':' + PAPER +
                              '/verification/reference-recovery.json'))['dependency_sources']
    need(base == set(reference), 'Baseline set differs from preserved 722')
    need((len(base), len(new), len(modules)) == (722, 15, 737), 'Wrong union sizes')
    source = {n: blob(e) for n, e in modules.items()}
    for n in base:
        need(digest(source[n]) == reference[n], 'Baseline source differs: ' + n)
    old = json.loads(git('show', m['source'] +
        ':flow-continuation-drafts/20261021-correct-output/SOURCE_BINDINGS.json'))['resolved_flow_sources']
    expected_new = {n for n, e in old.items() if e['provenance'] != 'baseline-ea1dfba'}
    need(new == expected_new, 'New module set differs from reviewed source checkpoint')
    for n in new:
        need(digest(source[n]) == old[n]['sha256'], 'Reviewed new source differs: ' + n)
    order, visiting, done = [], set(), set()
    def visit(n):
        need(n in source, 'Missing Flow import: ' + n)
        if n in done:
            return
        need(n not in visiting, 'Import cycle: ' + n)
        visiting.add(n)
        for dep in imports(source[n]):
            visit(dep)
        visiting.remove(n)
        done.add(n)
        order.append(n)
    for n in sorted(modules):
        visit(n)
    # These gates and toolchain pins must remain byte-identical in the candidate.
    guards = ['.github/workflows/lean.yml', 'scripts/ReferenceKernelCheck.py',
              'scripts/CheckReferenceRecovery.py', 'lean-toolchain', 'lake-manifest.json',
              'lakefile.toml', PAPER + '/verification/ReferenceAxiomAudit.lean']
    for path in guards:
        need((REPO / path).read_bytes() == git('show', m['baseline'] + ':' + path),
             'Preserved guard changed: ' + path)
    fixtures = {n: blob(e) for n, e in m['fixtures'].items()}
    return m, base, new, source, order, fixtures


def audit_source(modules, new):
    template = (HERE / 'AuditBody.lean').read_text()
    header = '\n'.join(l for l in template.splitlines() if l.startswith('import '))
    body = '\n'.join(l for l in template.splitlines() if not l.startswith('import '))
    def array(name, values):
        return 'def ' + name + ' : Array Lean.Name := #[' + ',\n'.join('`' + v for v in sorted(values)) + ']\n'
    return ('\n'.join('import ' + n for n in sorted(modules)) + '\n' + header + '\n' +
            array('flowExpectedModules', modules) + array('flowNewModules', new) +
            array('flowRequiredRoots', REQUIRED if new else []) + body + '\n')


def parse_audit(text, expected, new):
    modules = re.findall(r'^MODULE (.+)$', text, re.M)
    need(len(modules) == len(set(modules)) and set(modules) == expected, 'Audit module set mismatch')
    entries = re.findall(r'^ATTR ([^|]+)\|(.+)$', text, re.M)
    owners = {name: module for module, name in entries}
    need(len(owners) == len(entries) and set(owners.values()) == expected, 'Owned declaration inventory mismatch')
    roots = re.findall(r'^ROOT ([^|]+)\|(.+)$', text, re.M)
    wanted = {(module, name) for name, module in owners.items() if module in new}
    need(len(roots) == len(set(roots)) and set(roots) == wanted, 'New type/body roots are incomplete')
    need(not new or set(REQUIRED) <= {n for _, n in roots}, 'Missing explicit correctness roots')
    passes = re.findall(r'^AUDIT_PASS modules=(\d+) declarations=(\d+) roots=(\d+) closure=(\d+)$', text, re.M)
    need(len(passes) == 1, 'Missing or duplicate terminal audit success')
    need(tuple(map(int, passes[0][:3])) == (len(expected), len(owners), len(roots)), 'Audit count mismatch')
    return owners


def baseline_ci(run_id, commit):
    raw = subprocess.check_output(['gh', 'api',
        f'repos/gbodwin/paper-formalizations/actions/runs/{run_id}'], cwd=REPO, timeout=30)
    run = json.loads(raw)
    need(run['head_sha'] == commit and run['status'] == 'completed' and
         run['conclusion'] == 'success' and run['path'] == '.github/workflows/lean.yml',
         'Baseline CI is not successful at the exact candidate commit')
    jobs = json.loads(subprocess.check_output(['gh', 'api',
        f'repos/gbodwin/paper-formalizations/actions/runs/{run_id}/jobs?filter=latest&per_page=100'], timeout=30))
    need(jobs['total_count'] == len(jobs['jobs']) and jobs['jobs'], 'Incomplete baseline job evidence')
    need(all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs']),
         'Required baseline job did not succeed')
    return {'run': run, 'jobs': jobs}


def fixture_arguments(name, path, cap):
    if name == 'degenerate':
        return ['--run', str(path), 'all']
    if name.startswith('positive-'):
        return ['--run', str(path), str(cap)]
    return [str(path)]  # Envelope source contains its own #eval.


def fixture_pass(name, text):
    if name == 'degenerate':
        cases = re.findall(r'^PASS final dispatcher physical degenerate (\S+) ', text, re.M)
        expected = {'empty', 'one-zero-no-demands', 'self-demand', 'two-unit-direct'}
        need(len(cases) == 4 and set(cases) == expected, 'Missing physical degenerate executions')
    elif name == 'envelope':
        cases = re.findall(r'^PASS numerical final-dispatch envelope (\S+) ', text, re.M)
        expected = {'empty', 'singleton-no-demands', 'singleton-self-demand',
                    'padded-zero-repeated-demands', 'padded-half-dense', 'mixed-sparse', 'four-rationals'}
        need(len(cases) == 7 and set(cases) == expected, 'Missing numerical envelope cases')
    else:
        marker = ('PASS_PHYSICAL positive full dispatcher; orderedStates=9 ' if name == 'positive-physical'
                  else 'NATURAL_DIAGNOSTIC_MATCH_ONLY orderedStates=9 ')
        need(sum(l.startswith(marker) for l in text.splitlines()) == 1, 'Missing terminal fixture marker: ' + name)


def execute(args, m, base, new, source, order, fixtures):
    need(re.fullmatch('[0-9a-f]{40}', args.expected_commit or '') is not None, 'Full expected commit required')
    need(git('rev-parse', 'HEAD').decode().strip() == args.expected_commit, 'HEAD differs from expected commit')
    need(not git('status', '--porcelain', '--untracked-files=all').strip(), 'Execution needs a clean checkout')
    need(args.positive_attempt_cap is not None and args.positive_attempt_cap > 0, 'Explicit positive physical attempt cap required')
    need(args.baseline_run_id is not None, 'Exact-commit baseline CI run ID required')
    ci = baseline_ci(args.baseline_run_id, args.expected_commit)
    out = Path(args.output).resolve()
    report = {'status': 'running', 'commit': args.expected_commit, 'baseline_ci': ci,
              'compiled': [], 'replayed': [], 'commands': [], 'acceptance': False,
              'source_bindings': m,
              'validator_bindings': validator_snapshot()}
    started = time.monotonic()
    lock = open('/tmp/flow-ordinary-compiler.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    need(not set(subprocess.check_output(['ps', '-eo', 'comm='], text=True).split()) &
         {'lean', 'lake', 'leanchecker'}, 'Another compiler/build process is active')
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    snapshots = {}
    def command(label, argv, cap, extra_env=None):
        need(time.monotonic() - started < 12000, '200-minute execution budget exhausted')
        log = out / (label + '.log')
        receipt = {'label': label, 'argv': argv, 'cap_seconds': cap, 'returncode': None}
        report['commands'].append(receipt)
        (out / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
        with log.open('w') as stream:
            p = subprocess.Popen(argv, cwd=REPO, env=extra_env or env, stdout=stream,
                stderr=subprocess.STDOUT, start_new_session=True, pass_fds=(lock.fileno(),))
            try:
                receipt['returncode'] = p.wait(timeout=min(cap, max(1, 12000-(time.monotonic()-started))))
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                receipt['returncode'] = 124
        receipt['log_sha256'] = digest(log.read_bytes())
        print(label, receipt['returncode'], flush=True)
        need(receipt['returncode'] == 0, 'Failed gate: ' + label)
        return log.read_text()
    try:
        # Setup happens before the gate; no cache/build action may run concurrently.
        lean = command('lean-path', ['lake', 'env', 'which', 'lean'], 30).strip()
        checker = command('checker-path', ['lake', 'env', 'which', 'leanchecker'], 30).strip()
        need('version 4.34.0' in command('lean-version', [lean, '--version'], 30), 'Unexpected Lean version')
        package_manifest = json.loads((REPO / 'lake-manifest.json').read_text())
        package_roots = []
        for package in package_manifest['packages']:
            need(package['type'] == 'git', 'Unpinned non-Git dependency')
            root = REPO / package_manifest['packagesDir'] / package['name']
            head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], timeout=30).decode().strip()
            need(head == package['rev'], 'Installed package revision differs: ' + package['name'])
            need(not subprocess.check_output(['git', '-C', str(root), 'diff', 'HEAD', '--'], timeout=30),
                 'Installed package source is dirty: ' + package['name'])
            package_roots.append(root.resolve())
        paths = command('dependency-path', ['lake', 'env', 'printenv', 'LEAN_PATH'], 30).strip().split(':')
        sysroot = Path(command('lean-prefix', [lean, '--print-prefix'], 30).strip()).resolve()
        dependency_paths = []
        for path in paths:
            p = Path(path)
            if not p.is_absolute():
                p = REPO / p
            p = p.resolve()
            if p == (REPO / '.lake/build/lib/lean').resolve():
                continue  # Never load pre-existing project objects.
            need(p == sysroot / 'lib/lean' or any(p.is_relative_to(root) for root in package_roots),
                 'Unpinned dependency search path: ' + str(p))
            need(not (p / 'DirectedFlowCutGap').exists(), 'Dependency path shadows Flow')
            dependency_paths.append(p)
        # Bind runtime bytes and detect additions/removals or mutations after all gates.
        def runtime_snapshot():
            files = {Path(lean), Path(checker)}
            for root in [*dependency_paths, sysroot / 'lib/lean']:
                if root.exists():
                    files.update(p for p in root.rglob('*') if p.is_file())
            return {str(p): digest(p.read_bytes()) for p in sorted(files)}
        snapshots = runtime_snapshot()
        (out / 'runtime-bindings.json').write_text(json.dumps(snapshots, indent=2))
        lib, src = out / 'lib', out / 'src'
        lib.mkdir(); src.mkdir()
        env['LEAN_PATH'] = ':'.join(map(str, [lib, *dependency_paths]))
        for n in order:
            path = src / (n.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(source[n])
            obj = lib / (n.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            command('compile-' + n, [lean, '-j1', '--root=' + str(src), '-DautoImplicit=false', '-DwarningAsError=true',
                    '-o', str(obj), str(path)], 180)
            report['compiled'].append(n)
        inventories = {}
        for label, selected, additions in [('baseline-audit', base, set()), ('union-audit', set(source), new)]:
            path = out / (label + '.lean')
            path.write_text(audit_source(selected, additions))
            log = command(label, [lean, '-j1', '-DautoImplicit=false', '-DwarningAsError=true', str(path)], 600)
            inventories[label] = parse_audit(log, selected, additions)
        old, current = inventories['baseline-audit'], inventories['union-audit']
        need(len(old) == 26090, 'Fresh baseline declaration count differs from historical binding')
        need(all(current.get(n) == owner for n, owner in old.items()), 'Lost/reowned baseline declarations')
        need(all(current[n] in new for n in current.keys()-old.keys()), 'Addition owned outside new modules')
        report['declarations'] = inventories
        for n in sorted(source):
            command('replay-' + n, [checker, '-v', n], 300)
            report['replayed'].append(n)
        need(set(report['replayed']) == base | new and len(report['replayed']) == 737, 'Incomplete replay union')
        for name, data in fixtures.items():
            (out / (name + '.lean')).write_bytes(data)
        support = out / 'FinalDispatchPositiveFixtureSupport.lean'
        support.write_bytes(fixtures['positive-support'])
        command('positive-support', [lean, '-j1', '--root=' + str(out), '-DautoImplicit=false', '-DwarningAsError=true',
                '-o', str(lib / 'FinalDispatchPositiveFixtureSupport.olean'), str(support)], 180)
        for name in ['degenerate', 'envelope', 'positive-natural', 'positive-physical']:
            cmd = [lean, '-j1', '-DautoImplicit=false', '-DwarningAsError=true']
            cmd += fixture_arguments(name, out / (name + '.lean'), args.positive_attempt_cap)
            fixture_pass(name, command('fixture-' + name, cmd, 120))
        # Common final postflight below decides whether this status may survive.
        report['status'] = 'gates_passed_pending_independent_review'
    except BaseException as exc:
        report['status'] = 'failed'
        report['error'] = str(exc)
        raise
    finally:
        postflight_identity(report, args.expected_commit, source, out)
        try:
            plan()
            report['source_postflight_passed'] = not git('status', '--porcelain', '--untracked-files=all').strip()
            report['runtime_postflight_passed'] = bool(snapshots) and runtime_snapshot() == snapshots
            if not report['source_postflight_passed'] or not report['runtime_postflight_passed']:
                report['status'] = 'failed'
        except Exception as postflight:
            report['status'] = 'failed'
            report['postflight_error'] = str(postflight)
        report['elapsed_seconds'] = time.monotonic() - started
        report['objects'] = {str(p.relative_to(out)): digest(p.read_bytes())
                             for p in out.rglob('*.olean')}
        (out / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
        (out / 'SHA256SUMS').write_text(''.join(digest(p.read_bytes()) + '  ' + str(p.relative_to(out)) + '\n'
            for p in sorted(out.rglob('*')) if p.is_file() and p.name != 'SHA256SUMS'))
        fcntl.flock(lock, fcntl.LOCK_UN); lock.close()
    need(report['status'] == 'gates_passed_pending_independent_review', 'Postflight failed')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--execute', action='store_true')
    p.add_argument('--expected-commit')
    p.add_argument('--baseline-run-id', type=int)
    p.add_argument('--positive-attempt-cap', type=int)
    p.add_argument('--output', default='/tmp/flow-737-evidence')
    args = p.parse_args()
    if args.execute:
        out = Path(args.output).resolve()
        # Invalid/existing destinations are never modified. The workflow's
        # independent setup receipt still records this command failure.
        need(not out.exists() and not out.is_relative_to(REPO), 'Use a fresh output directory outside checkout')
        out.mkdir(parents=True)
        try:
            data = plan()
            execute(args, *data)
        except BaseException as exc:
            receipt = out / 'receipt.json'
            if not receipt.exists():
                receipt.write_text(json.dumps({'status': 'failed_preflight',
                    'expected_commit': args.expected_commit, 'baseline_run_id': args.baseline_run_id,
                    'error': str(exc), 'acceptance': False, 'compiled': [], 'replayed': [],
                    'validator_bindings': validator_snapshot()},
                    indent=2) + '\n')
            raise
        finally:
            (out / 'SHA256SUMS').write_text(''.join(digest(p.read_bytes()) + '  ' + str(p.relative_to(out)) + '\n'
                for p in sorted(out.rglob('*')) if p.is_file() and p.name != 'SHA256SUMS'))
    else:
        plan()
        print('SOURCE_ONLY_PREFLIGHT: exact 722 + 15 = 737; no Lean run', flush=True)


if __name__ == '__main__':
    main()
