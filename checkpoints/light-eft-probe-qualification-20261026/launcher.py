"""SOURCE ONLY: genuine native HeaderProbe elaboration, never a Python fixture.

The exact accepted native supervisor/limits/lifecycle are reused unchanged.
Success does not execute probe main, test SDK, replay a theorem or accept a job.
"""
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

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ENGINE = ROOT / 'checkpoints/light-eft-canonical-output-adapter-20261020'
WORKFLOW = '.github/workflows/light-eft-probe-qualification.yml'
BRANCH = 'refs/heads/light-eft-spanners-checkpoints'
PROBE = 'checkpoints/light-eft-global-replay-batches-20261026/HeaderProbe.lean'
PROBE_SHA = '135bec064c23826304376471a89eb630360d9db75b22154be9e109e9294355c9'
PARENT = '6f4513da54ffa6bf82ef0c58030341cfb417f33c'
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
            e.get('GITHUB_JOB') == 'native_probe_compile' and e.get('LEAN_NUM_THREADS') == '1',
            'Wrong actual native qualification source/job')
    require(len(head) == 40 and all(c in '0123456789abcdef' for c in head) and
            all(e.get(k, '').isdecimal() and int(e[k]) > 0
                for k in ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Invalid source/run/attempt')
    repo = e['GITHUB_REPOSITORY']
    require(e.get('GITHUB_WORKFLOW') == 'LightEFT probe native elaboration qualification' and
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
                'LIGHTEFT_JOB_WORKFLOW_SHA', 'LIGHTEFT_JOB_WORKFLOW_REF']}
    temp = Path(e['RUNNER_TEMP'])
    require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(), 'Unsafe temporary root')
    root = temp / ('light-eft-probe-elaboration-' + e['GITHUB_RUN_ID'] + '-' + e['GITHUB_RUN_ATTEMPT'])
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
        authenticate()
        require((ROOT / PROBE).stat().st_size == 5883 and
                hashlib.sha256((ROOT / PROBE).read_bytes()).hexdigest() == PROBE_SHA,
                'Actual production HeaderProbe source differs')
        profile = json.loads((HERE / 'profile.json').read_bytes())
        require(profile['scope'] == 'NATIVE_HEADER_PROBE_ELABORATION_ONLY' and
                profile['synthetic_fixture'] is False and profile['API_runtime_exercised'] is False and
                profile['production_acceptance'] is False, 'Qualification scope differs')
        tool = temp / 'lean-4.34.0-linux'
        require(tool.is_dir() and not tool.is_symlink() and not os.path.lexists(ROOT / '.lake') and
                (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0',
                'Not the fresh minimal official toolchain-only route')
        sys.pycache_prefix = str(root / 'absent-python-cache')
        require(not os.path.lexists(sys.pycache_prefix), 'Python cache prefix exists')
        sys.path[:0] = [str(ENGINE), str(ROOT / 'scripts')]
        from contracts import bind, save, unchanged, object_outputs
        from ci_inventory import CIInventory, CIIdentityGuard
        from ci_accounting import CIAccounting
        from ci_lease import CILease
        from LightEFTCgroup import memory_snapshot
        import child_runner
        from pilot_child import LIMITS
        require(LIMITS['RLIMIT_AS'] == 12 * 1024**3 and LIMITS['RLIMIT_CPU'] == 60 and
                LIMITS['RLIMIT_CORE'] == 0 and child_runner.DEADLINE == 90 and
                child_runner.PREFLIGHT_DEADLINE == 300 and child_runner.RSS_STOP == 6 * 1024**3 and
                child_runner.ANON_GROWTH_STOP == 3 * 1024**3 and
                child_runner.STOP_HEADROOM == 1024**3 and child_runner.INTERVAL == .1,
                'Accepted native resource/lifecycle envelope changed')
        source = {str(ROOT / r['path']): bind(ROOT / r['path'], r) for r in rows}
        for p in [HERE / 'bindings.json', ROOT / WORKFLOW, tool / 'bin/lean', tool / 'bin/leanchecker']:
            source[str(p)] = bind(p)
        require(source[str(tool / 'bin/lean')]['sha256'] == LEAN and
                source[str(tool / 'bin/leanchecker')]['sha256'] == CHECKER, 'Official native binaries differ')
        account = CIAccounting(memory_snapshot); baseline = account.sample()
        save(root / 'initial-admission-sample.json', baseline)
        require(baseline['headroom'] >= 8 * 1024**3 and baseline['system_available'] >= 8 * 1024**3,
                'Fresh outer8GiB constrained/host admission failed')
        child_runner.assert_idle('native-probe-before-claim', {})
        work = root / 'work'; work.mkdir(mode=0o700)
        objects = work / 'objects'; objects.mkdir(mode=0o700)
        audit = work / 'empty-audit'; audit.mkdir(mode=0o700)
        target = objects / 'HeaderProbe.olean'
        plan = dict(stage='compile', module='HeaderProbe', argv=[str(tool / 'bin/lean'),
                    '-j1', '-s65536', '-M5120', '-DautoImplicit=false', '-DwarningAsError=true',
                    '--root=' + str((ROOT / PROBE).parent), '-o', str(target), str(ROOT / PROBE)],
                    env=dict(LANG='C.UTF-8', LC_ALL='C.UTF-8', LEAN_NUM_THREADS='1',
                             LEAN_SYSROOT=str(tool), LEAN_PATH=str(tool / 'lib/lean'),
                             LEAN_SRC_PATH=str(tool / 'src/lean'),
                             MIMALLOC_ARENA_RESERVE='128MiB', MIMALLOC_VERBOSE='1'), cwd=str(work))
        frozen = json.dumps(plan, sort_keys=True)
        require(len(json.dumps({k: plan[k] for k in ['stage', 'argv', 'env']}).encode()) <= 4096,
                'Existing native launcher configuration bound exceeded')
        save(root / 'submitted-plan.json', dict(identity=identity, plan=plan, profile=profile,
             source_bindings=source, API_runtime_exercised=False, production_acceptance=False))

        class NativeContext:
            fixture = False; source_commit = head; wrapper_commit = head
            def __init__(self, lease):
                self.lease = lease; self.lock = lease.file; self.acquired_ns = lease.acquired_ns
                self.preservation_failed = False; self.guard = None; self.inputs = dict(source)
                self.inventory = CIInventory([tool / 'lib/lean'], tool, bind)
            def visible_gate(self, p):
                return 8 * 1024**3
            def verify(self, p):
                require(json.dumps(p, sort_keys=True) == frozen and p['stage'] == 'compile' and
                        p['argv'][0] == str(tool / 'bin/lean') and p['argv'][-1] == str(ROOT / PROBE),
                        'Changed native compiler command/env/stage')
                self.lease.check(); authenticate(); unchanged(source)
                require(not list(audit.iterdir()), 'Unexpected audit export')
            def before_child(self, p, receipt, persist):
                self.verify(p)
                receipt.update(native_qualification='NATIVE_HEADER_PROBE_ELABORATION_ONLY',
                    API_runtime_exercised=False, qualification_only=True, production_acceptance=False,
                    synthetic_fixture=False, working_directory=str(work), planned_command=plan,
                    legacy_scope_field_not_current_import_authority=True,
                    output_guard_spec=dict(stage='compile', objects=str(objects), target=str(target),
                                           audit=str(audit), protected=self.inputs))
                persist()
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
                     qualification='Fresh exact inventory under existing semantic/exclusion policy; no authenticated cache provenance'))
                receipt['native_input_files'] = len(self.inputs); persist()
            def prepare_child(self, p, receipt, persist, accounting):
                self.verify(p); child_runner.assert_idle('native-probe-preflight', receipt)
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
                               preexec_native_qualification_admission=now)
                persist()
            def after_child(self, p, receipt, persist):
                self.verify(p)
                if self.guard is not None:
                    self.inventory.scan(); self.guard.verify()
                if receipt.get('exit') == 0 and 'failure' not in receipt:
                    outputs = object_outputs(objects, target, True)
                    require(outputs and all(r['bytes'] <= 16 * 1024**2 for r in outputs.values()),
                            'Missing/oversized native compile outputs')
                    self.outputs = outputs; receipt['native_compilation_outputs'] = outputs
                receipt['native_inventory_completed'] = self.guard is not None
                receipt['between_child_preservation_passed'] = self.guard is not None
                persist()
            def complete_log(self, path, receipt, persist):
                receipt.setdefault('completed_logs', {})[path.name] = bind(path); persist()
            def output_summary(self):
                return dict(production_acceptance=False, API_runtime_exercised=False,
                            native_probe_outputs=getattr(self, 'outputs', {}))
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
        save(root / 'result-summary.json', dict(native_probe_elaboration_passed=True,
             qualification_only=True, synthetic_fixture=False, API_runtime_exercised=False,
             production_acceptance=False, identity=identity, attempt=receipt['attempt_id'],
             lease=lease.record, outputs=ctx.outputs))
    except BaseException as error:
        save(root / 'qualification-failure.json', dict(error=repr(error), traceback=traceback.format_exc(),
             qualification_only=True, production_acceptance=False))
        raise


if __name__ == '__main__':
    main()
