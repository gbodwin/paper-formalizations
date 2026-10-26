"""Qualification-only public Lake namespace capture; never a proof producer.

The ordinary metadata command finishes before direct supervisor exec. Native
admission, idle policy, CILease and child limits are not implemented or waived here.
"""
from pathlib import Path
import hashlib
import json
import os
import resource
import shutil
import signal
import stat
import subprocess
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = '81d897b4ccdbcdb01a047b655418c834bd56d547'
PUBLIC_FIELDS = ('LEAN_SYSROOT', 'LAKE', 'LEAN_PATH', 'LEAN_SRC_PATH')
IDENTITY_FIELDS = ('GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_REF',
    'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB', 'GITHUB_WORKFLOW',
    'GITHUB_WORKFLOW_SHA', 'GITHUB_WORKFLOW_REF', 'LEAN_NUM_THREADS',
    'LIGHTEFT_JOB_WORKFLOW_REPOSITORY', 'LIGHTEFT_JOB_WORKFLOW_PATH',
    'LIGHTEFT_JOB_WORKFLOW_SHA', 'LIGHTEFT_JOB_WORKFLOW_REF')
HELPER = '''import json,os,sys
keys=('LEAN_SYSROOT','LAKE','LEAN_PATH','LEAN_SRC_PATH')
values={k:os.environ[k] for k in keys}
if any(not v or len(v)>4096 or any(c in v for c in '\\0\\r\\n') for v in values.values()):
    raise SystemExit('Invalid public Lake field')
data=(json.dumps(values,sort_keys=True)+'\\n').encode()
if len(data)>16384: raise SystemExit('Public Lake record exceeds16KiB')
sys.stdout.buffer.write(data)
'''


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate metadata key')
        result[key] = value
    return result


def decoded(data):
    return json.loads(data, object_pairs_hook=no_duplicates)


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def signature(s):
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)


def read_regular(path, maximum):
    require(not any(p.is_symlink() for p in [path, *path.parents]), 'Symlink evidence path')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    with os.fdopen(fd, 'rb') as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode) and before.st_uid == os.getuid() and
                stat.S_IMODE(before.st_mode) == 0o600 and before.st_nlink == 1 and
                before.st_size <= maximum, 'Unsafe or oversized capture evidence')
        data = stream.read(maximum + 1)
        require(len(data) <= maximum and signature(before) == signature(os.fstat(stream.fileno())) ==
                signature(path.lstat()), 'Capture evidence changed')
    return data


def create(path, data):
    require(len(data) <= 65536, 'Bounded metadata record exceeded')
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW |
                 os.O_CLOEXEC, 0o600)
    with os.fdopen(fd, 'wb') as stream:
        stream.write(data); stream.flush(); os.fsync(stream.fileno())


def file_binding(path):
    b = read_regular(path, 65536)
    return dict(bytes=len(b), sha256=hashlib.sha256(b).hexdigest())


def _metadata_file_limit():
    # Lower only the short-lived metadata child's file limit. No native cap changes.
    resource.setrlimit(resource.RLIMIT_FSIZE, (65536, 65536))


def bounded_metadata(argv, folder, stem, timeout, stdout_limit):
    """Only the two fixed source-bound callers below use this helper.

    Failure stops the job; it is not a native-child or ECHILD qualification.
    Exit observation uses WNOWAIT. No poll/wait reaps the leader before a
    possible group signal. A reap-attempt marker precedes every reaping call;
    any interrupted/uncertain reap permanently forbids later group signals.
    """
    output = folder / (stem + '.stdout'); errors = folder / (stem + '.stderr')
    descriptors = []
    child = None
    reap_attempted = False
    ownership_uncertain = True
    record = dict(argv=argv, wall_limit_seconds=timeout, file_hard_limit=65536,
                  stdout_allowance=stdout_limit, started_ns=time.monotonic_ns(),
                  ordinary_metadata_only=True, native_acceptance=False)
    old_handlers = {}
    def interrupted(number, frame):
        raise RuntimeError('Metadata caller interrupted by signal ' + str(number))
    try:
        require(hasattr(os, 'WNOWAIT') and signal.getsignal(signal.SIGCHLD) == signal.SIG_DFL,
                'Require Linux non-reaping child observation and default SIGCHLD')
        for number in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            old_handlers[number] = signal.signal(number, interrupted)
        for path in (output, errors):
            descriptors.append(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                                        os.O_NOFOLLOW | os.O_CLOEXEC, 0o600))
        child = subprocess.Popen(argv, cwd=ROOT, stdin=subprocess.DEVNULL,
            stdout=descriptors[0], stderr=descriptors[1], start_new_session=True,
            preexec_fn=_metadata_file_limit)
        record['pid'] = child.pid
        deadline = time.monotonic() + timeout
        while True:
            # Set uncertainty before a syscall that may fail or be interrupted.
            # A successful WNOWAIT observation cannot reap or release this PID.
            ownership_uncertain = True
            observed = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
            ownership_uncertain = False
            if observed is not None:
                record['observed_exit'] = dict(code=observed.si_code, status=observed.si_status)
                require(observed.si_code == os.CLD_EXITED and observed.si_status == 0,
                        'Ordinary metadata command failed')
                break
            require(time.monotonic() < deadline, 'Ordinary metadata command timed out')
            time.sleep(.02)
        # This assignment MUST precede any call that can reap. Even if a Python
        # signal raises after kernel waitpid and before returncode assignment,
        # exception cleanup will never signal a potentially recycled group.
        reap_attempted = True
        code = child.wait(timeout=5)
        record.update(returncode=code, direct_waited=True)
        require(code == 0, 'Observed/waited metadata exit differs')
        require(len(read_regular(output, stdout_limit)) <= stdout_limit,
                'Metadata stdout allowance exceeded')
        read_regular(errors, 65536)
    except BaseException as error:
        record['error'] = repr(error)
        if child is not None and not reap_attempted and not ownership_uncertain:
            # Only WNOWAIT has observed this waitable child; no reap was attempted.
            # The single-threaded source has no SIGCHLD reaper and the PID is retained.
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except BaseException as cleanup_error:
                record.setdefault('cleanup_errors', []).append(repr(cleanup_error))
            try:
                reap_attempted = True
                record['returncode'] = child.wait(timeout=5)
                record['direct_waited'] = True
            except BaseException as cleanup_error:
                record.setdefault('cleanup_errors', []).append(repr(cleanup_error))
        if child is not None and (reap_attempted or ownership_uncertain) and not record.get('direct_waited'):
            record['cleanup_identity_or_reap_uncertain'] = True
            record['no_group_signal_after_reap_or_identity_uncertainty'] = True
        raise
    finally:
        record['reap_attempted'] = reap_attempted
        record['ownership_uncertain'] = ownership_uncertain
        for fd in descriptors:
            os.close(fd)
        for number, handler in old_handlers.items():
            signal.signal(number, handler)
        record['ended_ns'] = time.monotonic_ns()
        record['descendant_reaping_or_ECHILD_claim'] = False
        create(folder / (stem + '.command.json'), encoded(record))
    return output, errors, folder / (stem + '.command.json')


def process_snapshot(folder):
    return bounded_metadata(['/bin/ps', '-eo', 'pid,ppid,stat,comm'], folder,
                            'idle-processes-before-claim', 5, 65536)


def _identity(e):
    return {k: e[k] for k in IDENTITY_FIELDS}


def _self_start():
    return Path('/proc/self/stat').read_text().rsplit(')', 1)[1].split()[19]


def validate_capture(e):
    expected = Path(e['RUNNER_TEMP']) / ('light-eft-probe-main-capture-' +
                e['GITHUB_RUN_ID'] + '-' + e['GITHUB_RUN_ATTEMPT'])
    require(e.get('LIGHTEFT_LAKE_CAPTURE_DIR') == str(expected) and
            expected.is_absolute() and not expected.is_symlink(), 'Wrong fresh capture directory')
    s = expected.lstat()
    require(stat.S_ISDIR(s.st_mode) and s.st_uid == os.getuid() and
            stat.S_IMODE(s.st_mode) == 0o700, 'Unsafe capture directory')
    result = decoded(read_regular(expected / 'capture-result.json', 16384))
    require(result['state'] == 'successful_wait' and result['identity'] == _identity(e) and
            result['caller_pid'] == os.getpid() and result['caller_start'] == _self_start() and
            result['boot_id'] == Path('/proc/sys/kernel/random/boot_id').read_text().strip() and
            result['source_sha256'] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest() and
            result['bindings_sha256'] == e['LIGHTEFT_QUALIFICATION_BINDINGS_SHA'],
            'Capture is not this same source/run/process')
    start_path = expected / 'capture-start.json'
    start = decoded(read_regular(start_path, 16384))
    require(start['identity'] == _identity(e) and start['caller_pid'] == os.getpid() and
            start['caller_start'] == _self_start() and
            result['start'] == file_binding(start_path), 'Capture start binding differs')
    command_path = expected / 'lake-environment.command.json'
    command = decoded(read_regular(command_path, 16384))
    require(command.get('returncode') == 0 and command.get('direct_waited') is True and
            not command.get('error') and not command.get('cleanup_errors') and
            command['argv'] == [start['lake_entry'], 'env', '/usr/bin/python3', '-I', '-B', '-c', HELPER] and
            result['command'] == file_binding(command_path),
            'Lake environment command not successfully waited')
    paths = [expected / n for n in ['capture-start.json', 'capture-result.json',
             'lake-environment.stdout', 'lake-environment.stderr', 'lake-environment.command.json']]
    public_raw = read_regular(expected / 'lake-environment.stdout', 16384)
    public = decoded(public_raw)
    require(set(public) == set(PUBLIC_FIELDS) and
            all(isinstance(v, str) and v and len(v) <= 4096 and
                not any(c in v for c in '\0\r\n') for v in public.values()) and
            public == {k: e.get(k) for k in PUBLIC_FIELDS}, 'Captured public namespace differs')
    require(result['stdout'] == file_binding(expected / 'lake-environment.stdout') and
            result['stderr'] == file_binding(expected / 'lake-environment.stderr'),
            'Capture output byte binding differs')
    require(not (expected / 'capture-failure.json').exists(), 'Capture failure retained')
    for path in paths:
        read_regular(path, 65536)
    return paths


def main():
    require(sys.flags.isolated and sys.dont_write_bytecode and Path.cwd().resolve() == ROOT,
            'Require direct Python -I -B in the exact checkout')
    e = dict(os.environ)
    require('LIGHTEFT_LAKE_CAPTURE_DIR' not in e and e.get('GITHUB_ACTIONS') == 'true' and
            e.get('GITHUB_REPOSITORY') == 'gbodwin/paper-formalizations' and
            e.get('GITHUB_REF') == 'refs/heads/light-eft-spanners-checkpoints' and
            e.get('GITHUB_EVENT_NAME') == 'push' and e.get('GITHUB_JOB') == 'native_probe_main' and
            all(e.get(k, '').isdecimal() and int(e[k]) > 0 for k in
                ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Wrong fresh actual capture caller')
    temp = Path(e['RUNNER_TEMP'])
    require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(), 'Unsafe temporary root')
    folder = temp / ('light-eft-probe-main-capture-' + e['GITHUB_RUN_ID'] + '-' + e['GITHUB_RUN_ATTEMPT'])
    folder.mkdir(mode=0o700, exist_ok=False)
    require(signal.getitimer(signal.ITIMER_REAL) == (0.0, 0.0), 'Inherited caller alarm')
    old_alarm = signal.getsignal(signal.SIGALRM)
    def caller_expired(*_):
        raise TimeoutError('Ordinary capture caller exceeded90seconds')
    signal.signal(signal.SIGALRM, caller_expired); signal.setitimer(signal.ITIMER_REAL, 90)
    identity = _identity(e)
    def authenticate():
        def git(*args):
            return subprocess.run(['/usr/bin/git', *args], cwd=ROOT, check=True,
                                  capture_output=True, timeout=10).stdout
        require(git('rev-parse', 'HEAD').decode().strip() == e['GITHUB_SHA'] and
                git('show', '-s', '--format=%P', 'HEAD').decode().strip() == PARENT and
                not git('status', '--porcelain'), 'Capture source/parent/cleanliness differs')
        require(_identity(os.environ) == identity and e.get('LEAN_NUM_THREADS') == '1' and
                e.get('GITHUB_WORKFLOW') == 'LightEFT probe main profile qualification' and
                e.get('GITHUB_WORKFLOW_SHA') == e['GITHUB_SHA'] and
                e.get('GITHUB_WORKFLOW_REF') == e['GITHUB_REPOSITORY'] + '/' +
                    '.github/workflows/light-eft-probe-main-qualification.yml@' + e['GITHUB_REF'] and
                e.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY') == e['GITHUB_REPOSITORY'] and
                e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == '.github/workflows/light-eft-probe-main-qualification.yml' and
                e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == e['GITHUB_SHA'] and
                e.get('LIGHTEFT_JOB_WORKFLOW_REF') in
                    [e['GITHUB_REPOSITORY'] + '/.github/workflows/light-eft-probe-main-qualification.yml@' +
                     ref for ref in [e['GITHUB_REF'], e['GITHUB_SHA']]],
                'Actual capture workflow identity changed')
        raw = (HERE / 'bindings.json').read_bytes()
        require(hashlib.sha256(raw).hexdigest() == e['LIGHTEFT_QUALIFICATION_BINDINGS_SHA'],
                'Capture source binding seal differs')
        rows = decoded(raw)['files']
        require(0 < len(rows) <= 80 and len(rows) == len({r['path'] for r in rows}) and
                sum(r['bytes'] for r in rows) <= 2 * 1024**2, 'Capture source allowance exceeded')
        for row in rows:
            rel = Path(row['path']); path = ROOT / rel
            require(not rel.is_absolute() and '..' not in rel.parts and
                    not any(p.is_symlink() for p in [path, *path.parents]), 'Unsafe capture source')
            b = path.read_bytes()
            require(len(b) == row['bytes'] and hashlib.sha256(b).hexdigest() == row['sha256'] and
                    git('show', 'HEAD:' + rel.as_posix()) == b, 'Capture source hash differs')
    try:
        authenticate()
        lake = shutil.which('lake')
        require(lake is not None and Path(lake).is_absolute(), 'Ordinary setup Lake entry unavailable')
        create(folder / 'capture-start.json', encoded(dict(identity=_identity(e),
            caller_pid=os.getpid(), caller_start=_self_start(), lake_entry=lake,
            public_fields=list(PUBLIC_FIELDS), no_environment_or_token_dump=True)))
        output, errors, command = bounded_metadata(
            [lake, 'env', '/usr/bin/python3', '-I', '-B', '-c', HELPER],
            folder, 'lake-environment', 30, 16384)
        public = decoded(read_regular(output, 16384))
        require(set(public) == set(PUBLIC_FIELDS) and all(isinstance(v, str) and v and
                len(v) <= 4096 and not any(c in v for c in '\0\r\n') for v in public.values()),
                'Invalid public Lake namespace record')
        authenticate()
        create(folder / 'capture-result.json', encoded(dict(state='successful_wait',
            identity=_identity(e), caller_pid=os.getpid(), caller_start=_self_start(),
            boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            bindings_sha256=e['LIGHTEFT_QUALIFICATION_BINDINGS_SHA'],
            stdout=file_binding(output), stderr=file_binding(errors),
            start=file_binding(folder / 'capture-start.json'), command=file_binding(command))))
        direct = dict(e, **public, LIGHTEFT_LAKE_CAPTURE_DIR=str(folder))
        validate_capture(direct)
        signal.setitimer(signal.ITIMER_REAL, 0); signal.signal(signal.SIGALRM, old_alarm)
        # No live Lake wrapper surrounds the supervisor: successful wait precedes exec.
        os.execve('/usr/bin/python3', ['/usr/bin/python3', '-I', '-B', str(HERE / 'launcher.py')], direct)
    except BaseException as error:
        create(folder / 'capture-failure.json', encoded(dict(error=repr(error),
            traceback=traceback.format_exc()[-8192:], native_started=False,
            qualification_only=True, production_acceptance=False)))
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0); signal.signal(signal.SIGALRM, old_alarm)


if __name__ == '__main__':
    main()
