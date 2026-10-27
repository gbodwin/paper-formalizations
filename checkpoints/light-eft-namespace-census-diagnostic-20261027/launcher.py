"""Private source draft: genuine dual-source setup/census, never replay acceptance."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import signal
import stat
import subprocess
import sys
import time
import traceback
import types

HERE = Path(__file__).resolve().parent
HARNESS = HERE.parents[1]
TESTED = HARNESS.parent
TESTED_SHA = '2bc06c4aca8ba1e0d48e4e4a879f93944a17d4db'
PARENT = '42d83b6ad3e823f55324b46fb73c8c67d6141d5b'
WORKFLOW = '.github/workflows/light-eft-namespace-census-diagnostic.yml'
REL = 'checkpoints/light-eft-namespace-census-diagnostic-20261027'
ENGINE = TESTED / 'checkpoints/light-eft-canonical-output-adapter-20261020'
CONTRACT = 'checkpoints/light-eft-global-replay-batches-20261026/closure_contract.py'
CAPTURE = 'checkpoints/light-eft-probe-main-qualification-20261026/lake_capture.py'
MAX_RESULT = 1024 ** 2


def require(ok, text):
    if not ok:
        raise RuntimeError(text)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate census key')
        result[key] = value
    return result


def regular(path, limit):
    for p in [path, *path.parents]:
        require(not p.is_symlink(), 'Symlink census control/input')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as f:
        a = os.fstat(f.fileno())
        require(stat.S_ISREG(a.st_mode) and a.st_nlink == 1 and
                a.st_size <= limit, 'Unsafe/oversized census input')
        raw = f.read(limit + 1); z = os.fstat(f.fileno()); n = path.lstat()
        sig = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_nlink,
                         s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(len(raw) <= limit and sig(a) == sig(z) == sig(n), 'Census input changed')
        return raw


def create(path, raw):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'wb') as f:
        f.write(raw); f.flush(); os.fsync(f.fileno())


def git(root, *args):
    return subprocess.run(['/usr/bin/git', *args], cwd=root, check=True,
                          capture_output=True, timeout=10).stdout


def identity():
    e = os.environ
    require(Path(e['GITHUB_WORKSPACE']) == TESTED and HARNESS == TESTED / 'diagnostic-control' and
            Path.cwd() == TESTED, 'Wrong actual workspace/dual-checkout placement')
    for root in [HARNESS, TESTED]:
        for path in [root, *root.parents, root / '.git']:
            require(not path.is_symlink(), 'Symlink Git/workspace identity')
        require((root / '.git').is_dir() and not (root / '.git/commondir').exists() and
                not (root / '.git/objects/info/alternates').exists(),
                'Redirected/shared Git store')
    require(not any(e.get(k) for k in ['GIT_DIR', 'GIT_WORK_TREE', 'GIT_COMMON_DIR',
                'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES']),
            'Git environment redirects source')
    q = git(HARNESS, 'rev-parse', 'HEAD').decode().strip()
    require(len(q) == 40 and all(c in '0123456789abcdef' for c in q) and
            git(HARNESS, 'show', '-s', '--format=%P', 'HEAD').decode().strip() == PARENT,
            'Wrong sole-parent harness lineage')
    require(git(TESTED, 'rev-parse', 'HEAD').decode().strip() == TESTED_SHA and
            not git(TESTED, 'status', '--porcelain', '--untracked-files=no'),
            'Tested source identity/cleanliness differs')
    untracked = git(TESTED, 'ls-files', '--others', '--exclude-standard', '-z').split(b'\0')
    require(all(not p or p == b'diagnostic-control/' or p.startswith(b'diagnostic-control/') or
                p == b'.lake/' or p.startswith(b'.lake/') for p in untracked),
            'Unaccounted untracked tested input')
    require(not git(HARNESS, 'status', '--porcelain', '--untracked-files=all'),
            'Harness checkout is not clean')
    require(e.get('GITHUB_ACTIONS') == 'true' and
            e.get('GITHUB_REPOSITORY') == 'gbodwin/paper-formalizations' and
            e.get('GITHUB_EVENT_NAME') == 'push' and
            e.get('GITHUB_REF') == 'refs/heads/light-eft-spanners-checkpoints' and
            e.get('GITHUB_JOB') == 'observe_reacquired_namespace' and
            e.get('GITHUB_WORKFLOW') == 'LightEFT fresh namespace census diagnostic' and
            e.get('GITHUB_SHA') == e.get('GITHUB_WORKFLOW_SHA') == q and
            e.get('LEAN_NUM_THREADS') == '1', 'Wrong genuine census job')
    repo = e['GITHUB_REPOSITORY']; ref = e['GITHUB_REF']
    require(e.get('GITHUB_WORKFLOW_REF') == repo + '/' + WORKFLOW + '@' + ref and
            e.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY') == repo and
            e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == WORKFLOW and
            e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == q and
            e.get('LIGHTEFT_JOB_WORKFLOW_REF') in
            [repo + '/' + WORKFLOW + '@' + ref, repo + '/' + WORKFLOW + '@' + q] and
            all(e.get(k, '').isdecimal() and int(e[k]) > 0 for k in
                ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Actual workflow/source differs')
    return dict(harness=q, harness_parent=PARENT, tested=TESTED_SHA,
                tested_root=str(TESTED), harness_root=str(HARNESS),
                repository=repo, ref=ref, run=e['GITHUB_RUN_ID'],
                attempt=e['GITHUB_RUN_ATTEMPT'], job=e['GITHUB_JOB'])


def authenticate(ci):
    require(identity() == ci, 'Census identity drift')
    raw = regular(HERE / 'bindings.json', MAX_RESULT)
    sha = hashlib.sha256(raw).hexdigest()
    require(sha == os.environ['LIGHTEFT_CENSUS_BINDINGS_SHA'], 'Census bindings differ')
    m = json.loads(raw, object_pairs_hook=unique)
    require(m['schema'] == 'DUAL_SOURCE_NAMESPACE_CENSUS_BINDINGS_V1' and
            m['tested_source'] == TESTED_SHA and m['harness_parent'] == PARENT and
            0 < len(m['files']) <= 80 and
            sum(row['bytes'] for row in m['files']) <= 2 * 1024 ** 2,
            'Wrong finite source binding contract')
    require(len(m['files']) == len({(r['origin'], r['path']) for r in m['files']}),
            'Duplicate source binding')
    sources = {}
    for row in m['files']:
        require(row['origin'] in ['tested', 'harness'] and
                not Path(row['path']).is_absolute() and
                '..' not in Path(row['path']).parts, 'Unsafe source row')
        root = TESTED if row['origin'] == 'tested' else HARNESS
        data = regular(root / row['path'], row['bytes'])
        require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() ==
                row['sha256'] and data == git(root, 'show', 'HEAD:' + row['path']),
                'Source not exact bound Git bytes: ' + row['path'])
        sources[(row['origin'], row['path'])] = data
    wf = regular(HARNESS / WORKFLOW, MAX_RESULT)
    require(wf == git(HARNESS, 'show', 'HEAD:' + WORKFLOW) and
            ('LIGHTEFT_CENSUS_BINDINGS_SHA: ' + sha).encode() in wf,
            'Actual workflow binding differs')
    return sources


def load(name, path, data):
    module = types.ModuleType(name); module.__file__ = str(path)
    exec(compile(data, str(path), 'exec'), module.__dict__)
    return module


def report_root(ci, fresh):
    temp = Path(os.environ['RUNNER_TEMP']).resolve(strict=True)
    require(temp.is_absolute() and not temp.is_symlink(), 'Unsafe runner temp')
    root = temp / ('light-eft-namespace-census-' + ci['run'] + '-' + ci['attempt'])
    if fresh:
        root.mkdir(mode=0o700, exist_ok=False)
    s = root.lstat()
    require(stat.S_ISDIR(s.st_mode) and s.st_uid == os.getuid() and
            stat.S_IMODE(s.st_mode) == 0o700, 'Unsafe census evidence domain')
    return root


def source_setup(ci, root, cl):
    require(not os.path.lexists(TESTED / '.lake'), 'Inherited package/cache tree')
    require((TESTED / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0',
            'Toolchain pin differs')
    m = json.loads(regular(TESTED / 'lake-manifest.json', MAX_RESULT), object_pairs_hook=unique)
    packages = m['packages']
    require(m['packagesDir'] == '.lake/packages' and len(packages) == 9 and
            len({p['name'] for p in packages}) == 9 and
            {p['name']: p['rev'] for p in packages} == cl.PINS and
            all(p['type'] == 'git' and p['subDir'] is None and
                p['url'].startswith('https://github.com/') and
                not any(c in p['url'] for c in ['@', '?', '#', '\n', '\r'])
                for p in packages), 'Exact public source manifest differs')
    folder = root / 'source-setup'; folder.mkdir(mode=0o700)
    result = dict(status='FAILED_SOURCE_SETUP_ONLY', identity=ci, packages=[],
                  proof_acceptance=False, historical_objects_consumed=False)
    def command(argv, cwd, label):
        argv = ['/usr/bin/git', '-c', 'core.hooksPath=/dev/null',
                '-c', 'core.fsmonitor=false', *argv]
        record = dict(argv=argv, cwd=str(cwd), timeout_seconds=600,
                      started_ns=time.monotonic_ns())
        create(folder / (label + '-start.json'), encoded(record))
        try:
            p = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=600)
        except (subprocess.TimeoutExpired, OSError) as error:
            for suffix in ['stdout', 'stderr']:
                value = getattr(error, suffix, None)
                create(folder / (label + '.' + suffix),
                       value.encode() if isinstance(value, str) else (value or b''))
            create(folder / (label + '.json'), encoded(dict(record, error=repr(error),
                returncode=None, partials_preserved=True, retry=False)))
            raise
        create(folder / (label + '.stdout'), p.stdout)
        create(folder / (label + '.stderr'), p.stderr)
        create(folder / (label + '.json'), encoded(dict(record,
            ended_ns=time.monotonic_ns(), returncode=p.returncode)))
        require(p.returncode == 0, 'Source acquisition failed: ' + label)
        return p.stdout
    try:
        (TESTED / '.lake').mkdir(mode=0o700)
        base = TESTED / '.lake/packages'; base.mkdir(mode=0o700)
        for p in packages:
            name = p['name']; dest = base / name
            require(name in cl.PINS and not os.path.lexists(dest), 'Existing package destination')
            dest.mkdir(mode=0o700)
            command(['init', '--quiet'], dest, name + '-init')
            command(['remote', 'add', 'origin', p['url']], dest, name + '-origin')
            command(['fetch', '--no-tags', '--depth=1', 'origin', p['rev']], dest, name + '-fetch')
            rev = command(['rev-parse', 'FETCH_HEAD'], dest, name + '-fetched').decode().strip()
            require(rev == cl.PINS[name], 'Fetched package revision differs')
            command(['checkout', '--detach', '--quiet', rev], dest, name + '-checkout')
            require(command(['rev-parse', 'HEAD'], dest, name + '-head').decode().strip() == rev and
                    not command(['status', '--porcelain', '--untracked-files=all'], dest, name + '-status') and
                    not os.path.lexists(dest / '.lake'), 'Package checkout/cache differs')
            result['packages'].append(dict(name=name, revision=rev, url=p['url']))
        authenticate(ci); cl.controls()
        result['status'] = 'EXACT_PACKAGE_SOURCES_ONLY_NOT_COMPILED_INPUT_ACCEPTANCE'
    except BaseException as error:
        result.update(failure=repr(error), partial_source_checkouts_preserved=True)
        raise
    finally:
        create(folder / 'result.json', encoded(result))


def carrier_binding(cl, selected):
    """Observe indirections without replacing the selected multicall argv0."""
    require(isinstance(selected, str) and selected and len(selected) <= 4096 and
            not any(c in selected for c in '\0\r\n') and
            shutil.which('lake') == selected, 'Selected Lake carrier changed')
    path = Path(selected).absolute()
    current = Path(path.anchor)
    pending = list(path.parts[1:]); chain = []; links = 0; steps = 0
    def row(p, s):
        return dict(path=str(p), device=s.st_dev, inode=s.st_ino, uid=s.st_uid,
                    gid=s.st_gid, mode=s.st_mode, nlink=s.st_nlink)
    chain.append(row(current, current.lstat()))
    while pending:
        steps += 1
        require(steps <= 256, 'Carrier path component budget exceeded')
        name = pending.pop(0)
        if name in ['', '.']:
            continue
        if name == '..':
            current = current.parent; chain.append(row(current, current.lstat()))
            continue
        candidate = current / name; before = candidate.lstat()
        item = row(candidate, before)
        if stat.S_ISLNK(before.st_mode):
            links += 1
            require(links <= 40, 'Carrier symlink budget exceeded')
            target = os.readlink(candidate)
            require(target and len(target) <= 4096 and
                    cl.signature(before) == cl.signature(candidate.lstat()),
                    'Carrier indirection changed while reading')
            item.update(target=target, size=before.st_size,
                        mtime_ns=before.st_mtime_ns, ctime_ns=before.st_ctime_ns)
            chain.append(item)
            target = Path(target)
            if target.is_absolute():
                current = Path(target.anchor); chain.append(row(current, current.lstat()))
                pending = list(target.parts[1:]) + pending
            else:
                pending = list(target.parts) + pending
        else:
            require(stat.S_ISDIR(before.st_mode) or
                    (stat.S_ISREG(before.st_mode) and not pending),
                    'Carrier path contains an unsupported component')
            chain.append(item); current = candidate
    require(stat.S_ISREG(current.lstat().st_mode), 'Resolved carrier is not regular')
    record = dict(selected_argv0=selected, lexical_absolute=str(path), cwd=str(Path.cwd()),
                  path_environment_sha256=hashlib.sha256(os.environ.get('PATH', '').encode()).hexdigest(),
                  chain=chain, resolved_path=str(current), resolved=cl.observation(current))
    require(len(encoded(record)) <= 16384, 'Complete carrier binding exceeds16KiB')
    return record


def observe(ci, root, cl, sources):
    setup = json.loads(regular(root / 'source-setup/result.json', MAX_RESULT), object_pairs_hook=unique)
    require(setup['identity'] == ci and setup['status'] ==
            'EXACT_PACKAGE_SOURCES_ONLY_NOT_COMPILED_INPUT_ACCEPTANCE', 'No exact fresh source setup')
    capture = root / 'public-capture'; capture.mkdir(mode=0o700)
    cap = load('_bound_public_census_capture', TESTED / CAPTURE, sources[('tested', CAPTURE)])
    lake = shutil.which('lake')
    require(lake is not None, 'No installed Lake carrier')
    carrier = carrier_binding(cl, lake)
    create(capture / 'lake-carrier-before.json', encoded(carrier))
    try:
        # Keep the original selected spelling: resolving argv0 can change elan
        # multicall dispatch. The resolved path is used only for observation.
        cap.bounded_metadata([lake, 'env', '/usr/bin/python3', '-I', '-B', '-c', cap.HELPER],
                             capture, 'lake-environment', 30, 16384)
    finally:
        try:
            after = carrier_binding(cl, lake)
        except BaseException as error:
            create(capture / 'lake-carrier-after.json', encoded(dict(
                observation_failed=True, error=repr(error), accepted=False)))
            raise
        create(capture / 'lake-carrier-after.json', encoded(after))
        require(after == carrier, 'Lake carrier changed across waited capture')
    public = json.loads(regular(capture / 'lake-environment.stdout', 16384), object_pairs_hook=unique)
    require(set(public) == set(cap.PUBLIC_FIELDS) and
            all(isinstance(v, str) and v and len(v) <= 4096 and
                not any(c in v for c in '\0\r\n') for v in public.values()), 'Unsafe public capture')
    # These three fields are the only runtime() inputs. LEAN_SRC_PATH remains
    # captured verbatim, bound below, and is not consumed by this namespace job.
    os.environ.update({k: public[k] for k in ['LEAN_SYSROOT', 'LAKE', 'LEAN_PATH']})
    sys.path[:0] = [str(ENGINE), str(TESTED / 'scripts')]
    from LightEFTCgroup import memory_snapshot
    from ci_accounting import CIAccounting
    from ci_lease import CILease
    from contracts import bind, save, unchanged
    import child_runner
    account = CIAccounting(memory_snapshot); before = account.sample()
    create(root / 'initial-accounting.json', encoded(before))
    require(before['headroom'] >= 8 * 1024 ** 3 and
            before['system_available'] >= 8 * 1024 ** 3, 'Existing outer8GiB admission failed')
    cap.bounded_metadata(['/usr/bin/ps', '-eo', 'pid,ppid,stat,comm'],
                         capture, 'idle-processes', 10, 65536)
    idle = {}
    try:
        child_runner.assert_idle('namespace-before-claim', idle)
    finally:
        create(root / 'idle-before-claim.json', encoded(idle))
    source_bindings = {str((TESTED if origin == 'tested' else HARNESS) / path):
                       bind((TESTED if origin == 'tested' else HARNESS) / path)
                       for origin, path in sources}
    for path in [HERE / 'bindings.json', HARNESS / WORKFLOW,
                 Path(sys.executable).resolve(), capture / 'lake-environment.stdout',
                 capture / 'lake-environment.command.json',
                 capture / 'idle-processes.stdout', capture / 'idle-processes.command.json',
                 capture / 'lake-carrier-before.json', capture / 'lake-carrier-after.json',
                 Path('/usr/bin/ps')]:
        source_bindings[str(path)] = bind(path)
    tool, tools, roots, kinds = cl.runtime()
    for name in tools:
        path = tool / 'bin' / name; source_bindings[str(path)] = bind(path)
    work = root / 'work'; work.mkdir(mode=0o700)
    objects = root / 'empty-objects'; objects.mkdir(mode=0o700)
    audit = root / 'empty-audit'; audit.mkdir(mode=0o700)
    plan = dict(stage='compile', argv=[str(Path(sys.executable).resolve()), '-I', '-B',
                str(HERE / 'payload.py'), '--child', str(work)], cwd=str(work),
                env=dict(LANG='C.UTF-8', LC_ALL='C.UTF-8', PATH='/usr/bin:/bin',
                    LEAN_NUM_THREADS='1', MIMALLOC_ARENA_RESERVE='128MiB', MIMALLOC_VERBOSE='1',
                    LEAN_SYSROOT=public['LEAN_SYSROOT'], LAKE=public['LAKE'],
                    LEAN_PATH=public['LEAN_PATH'], CENSUS_TESTED_SOURCE=TESTED_SHA,
                    CENSUS_HARNESS_SHA=ci['harness'],
                    CENSUS_BINDINGS_SHA=os.environ['LIGHTEFT_CENSUS_BINDINGS_SHA']))
    def check_identity():
        require(identity() == ci, 'Actual census identity changed')
    frozen = None
    class Context:
        fixture = True
        source_commit = TESTED_SHA
        wrapper_commit = ci['harness']
        preservation_failed = False
        def __init__(self, lease):
            self.lease = lease; self.lock = lease.file; self.acquired_ns = lease.acquired_ns
        def visible_gate(self, p):
            return 8 * 1024 ** 3
        def verify(self, p):
            require(json.dumps(p, sort_keys=True) == frozen, 'Census command/env/cwd changed')
            self.lease.check(); unchanged(source_bindings); authenticate(ci); cl.controls()
            require(carrier_binding(cl, lake) == carrier, 'Protected Lake carrier drift')
            require(cl.runtime()[1:] == (tools, roots, kinds), 'Tool/package/runtime identity drift')
            require(not list(objects.iterdir()) and not list(audit.iterdir()), 'Unexpected native outputs')
        def before_child(self, p, record, persist):
            self.verify(p)
            record.update(stage_kind='ACTUAL_NAMESPACE_CENSUS_PYTHON_ONLY', diagnostic_only=True,
                production_acceptance=False, qualification_acceptance=False,
                selected_lake_carrier=carrier,
                resource_class='Unchanged non-audit Python fixture; no Lean invocation',
                planned_command=json.loads(frozen), working_directory=str(work),
                output_guard_spec=dict(stage='compile', objects=str(objects),
                    target=str(objects / 'NeverProduced.olean'), audit=str(audit),
                    protected=source_bindings))
            persist()
        def prepare_child(self, p, record, persist, accounting):
            self.verify(p); child_runner.assert_idle('namespace-preflight', record)
            now = accounting.sample(); record['initial_preflight_sample'] = now; persist()
            child_runner.check_memory(now, before, 8 * 1024 ** 3)
            require(now['system_available'] >= 8 * 1024 ** 3 and
                    shutil.disk_usage(work).free > 2 * 1024 ** 3, 'Fresh admission below boundary')
            return now
        def preexec(self, p, record, persist):
            self.verify(p)
            free = shutil.disk_usage(work).free
            require(free > 2 * 1024 ** 3, 'Fresh preexec disk below boundary')
            record.update(preexec_binding_verified=True, preexec_disk_bytes=free); persist()
        def after_child(self, p, record, persist):
            self.verify(p)
            if record.get('exit') == 0 and not record.get('failure'):
                result = json.loads(regular(work / 'result.json', MAX_RESULT), object_pairs_hook=unique)
                require(result['scope'] == 'ACTUAL_FRESH_NAMESPACE_CENSUS_ONLY' and
                        result['observer_completed'] is True and result['production_acceptance'] is False and
                        result['replay_invoked'] is False and result['checker_invocations'] == 0 and
                        result['tested_source'] == TESTED_SHA and result['harness_source'] == ci['harness'] and
                        result['bindings_sha256'] == os.environ['LIGHTEFT_CENSUS_BINDINGS_SHA'] and
                        result['ordered_roots'] == list(map(str, roots)) and result['root_kinds'] == kinds and
                        result['actual_tools'] == tools and result['namespace_after'] ==
                        cl.package_namespace(roots, kinds) == result['namespace_before'],
                        'Fresh actual census/source/preservation differs')
                require((root / 'runtime/raw.log').read_text().strip() ==
                        'ACTUAL_FRESH_NAMESPACE_CENSUS_COMPLETE_NOT_ACCEPTANCE', 'Wrong diagnostic marker')
                record['census_result'] = bind(work / 'result.json')
            record['between_child_preservation_passed'] = True; persist()
        def complete_log(self, path, record, persist):
            record.setdefault('completed_logs', {})[path.name] = bind(path); persist()
        def output_summary(self):
            return dict(production_acceptance=False, generated_Lean_objects=[], audit_exports=[])
    # Cancel only our source/admission alarm; the unchanged engine installs its
    # own300s preflight and90s whole-child limits. Ordinary setup was outside it.
    signal.setitimer(signal.ITIMER_REAL, 0)
    with CILease(root, save, check_identity) as lease:
        plan['env'].update(LIGHTEFT_DIAGNOSTIC_LOCK_FD=str(lease.file.fileno()),
                           LIGHTEFT_DIAGNOSTIC_LOCK_PATH=str(lease.path))
        frozen = json.dumps(plan, sort_keys=True)
        config = json.dumps({k: plan[k] for k in ['argv', 'env', 'stage']}).encode()
        create(root / 'submitted-plan-size.json', encoded(dict(bytes=len(config),
            sha256=hashlib.sha256(config).hexdigest(), limit=4096, accepted=False)))
        require(len(config) <= 4096, 'Launcher config exceeds unchanged4096 bound')
        save(root / 'submitted-plan.json', dict(identity=ci, plan=plan,
            source_bindings=source_bindings, actual_roots=list(map(str, roots)), root_kinds=kinds,
            protected_carrier=carrier,
            carrier_checks='Full selection/chain/bytes before capture, after wait, and before/preexec/after child; not a hostile-writer lease',
            historical_objects_consumed=False, public_field_not_consumed=['LEAN_SRC_PATH']))
        record = child_runner.run_child(plan, work, root / 'runtime', Context(lease), accounting=account)
        require(record['state'] == 'finished' and record['exit'] == 0 and
                not record.get('failure') and record.get('direct_reaped') is True and
                record.get('waitid_wait4_status_match') is True and
                record.get('kernel_no_children_verified') is True and
                record.get('all_descendants_gone') is True and not record.get('cleanup_errors'),
                'Incomplete Python census lifecycle')
    require(lease.record['state'] == 'released' and lease.record.get('kernel_echild') is True and
            not lease.record.get('release_errors'), 'Incomplete fresh census CI lease release')
    save(root / 'result-summary.json', dict(census_completed=True, identity=ci,
         production_acceptance=False, checker_invocations=0, historical_consumer_reconstruction=False,
         attempt=record['attempt_id'], lease=lease.record))


def main():
    require(sys.flags.isolated and sys.dont_write_bytecode and
            sys.argv[1:] in [['source-setup'], ['capture-and-census']], 'Fixed isolated census phase required')
    require(signal.getitimer(signal.ITIMER_REAL) == (0.0, 0.0), 'Existing source timer')
    old = signal.getsignal(signal.SIGALRM)
    def expired(*unused):
        raise TimeoutError('Census source/admission exceeded90 seconds')
    signal.signal(signal.SIGALRM, expired); signal.setitimer(signal.ITIMER_REAL, 90)
    root = None
    try:
        ci = identity(); root = report_root(ci, sys.argv[1] == 'source-setup')
        sources = authenticate(ci)
        cache = root / ('absent-parent-cache-' + sys.argv[1])
        require(not os.path.lexists(cache), 'Parent cache prefix exists')
        sys.pycache_prefix = str(cache)
        cl = load('_bound_tested_census_contract', TESTED / CONTRACT, sources[('tested', CONTRACT)])
        cl.controls()
        if sys.argv[1] == 'source-setup':
            signal.setitimer(signal.ITIMER_REAL, 0)
            source_setup(ci, root, cl)
        else:
            observe(ci, root, cl, sources)
    except BaseException as error:
        if root is not None:
            create(root / ('failure-' + sys.argv[1] + '.json'), encoded(dict(
                error=repr(error), partial=getattr(error, 'partial', None),
                traceback=traceback.format_exc(), production_acceptance=False)))
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0); signal.signal(signal.SIGALRM, old)


if __name__ == '__main__':
    main()
