"""One bounded, manifest-authorized, same-descriptor data-file advice pass."""
from pathlib import Path
import codecs
import datetime
import hashlib
import json
import os
import stat
import time
from collections import Counter
from pilot_cache_advice import signature

B = Path(__file__).resolve().parent
R = B.parents[1]
PLAN = B / 'recovery-plan.json'
PLAN_SHA = 'a0c6b1c10e7ce61df406d68f1b84b6418b3f1acb4d925c5fb20f6ea76a42e335'
LOG = B / 'finite-recovery.jsonl'
FILE_CEILING = 7313
BYTE_CEILING = 3104249317
LOG_BOUND = 8 * 1024**2


def read_plan():
    raw = PLAN.read_bytes()
    if hashlib.sha256(raw).hexdigest() != PLAN_SHA:
        raise RuntimeError('Recovery plan changed')
    plan = json.loads(raw)
    entries = plan['entries']
    if (len(entries) != FILE_CEILING or sum(x['bytes'] for x in entries) != BYTE_CEILING
            or len({x['path'] for x in entries}) != FILE_CEILING):
        raise RuntimeError('Recovery authority ceiling/membership mismatch')
    for item in plan['authority_manifests']:
        with (R / item['path']).open('rb') as f:
            if hashlib.file_digest(f, 'sha256').hexdigest() != item['sha256']:
                raise RuntimeError('Recovery authority manifest changed')
    return plan


def advise_one(row, roots, bound):
    rel = Path(row['path'])
    if rel.is_absolute() or '..' in rel.parts or len(rel.parts) < 3 or rel.parts[0] != 'checkpoints' or rel.parts[1] not in roots:
        raise RuntimeError('Recovery path outside exact authorized roots')
    path = R / rel
    out = {'path': str(rel), 'bytes': row['bytes']}
    def excluded(reason):
        return {**out, 'status': 'excluded', 'reason': reason}
    if str(path) in bound:
        return excluded('current_bound_input')
    if row.get('excluded'):
        return excluded(row['excluded'])
    if path.suffix not in {'.json', '.jsonl', '.txt', '.log', '.trace', '.maps'} or (path.suffix == '.txt' and 'source' in path.name.lower()):
        return excluded('code_object_or_nondata_extension')
    if any(p.is_symlink() for p in [path, *path.parents]):
        return excluded('symlink')
    try:
        observed = path.lstat()
        if not stat.S_ISREG(observed.st_mode):
            return excluded('nonregular')
        if observed.st_mode & 0o111:
            return excluded('executable_mode')
        if signature(observed) != row['identity']:
            return excluded('changed_identity')
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except FileNotFoundError:
        return excluded('changed_or_missing_path')
    with os.fdopen(fd, 'rb') as f:
        before = os.fstat(f.fileno())
        if not stat.S_ISREG(before.st_mode):
            return excluded('nonregular')
        if signature(before) != row['identity'] or before.st_size != row['bytes']:
            return excluded('changed_identity_or_size')
        digest = hashlib.sha256()
        decoder = codecs.getincrementaldecoder('utf-8')('strict')
        for block in iter(lambda: f.read(1024 * 1024), b''):
            if b'\0' in block:
                return excluded('binary_content')
            try:
                decoder.decode(block)
            except UnicodeDecodeError:
                return excluded('binary_content')
            digest.update(block)
        try:
            decoder.decode(b'', final=True)
        except UnicodeDecodeError:
            return excluded('binary_content')
        after = os.fstat(f.fileno())
        if signature(after) != signature(before) or digest.hexdigest() != row['sha256']:
            return excluded('changed_identity_or_hash')
        os.posix_fadvise(f.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        final = os.fstat(f.fileno())
        if signature(final) != signature(after):
            raise RuntimeError('Recovery file changed during advice: ' + str(rel))
        return {**out, 'status': 'advised', 'sha256': digest.hexdigest(),
                'identity': signature(after), 'identity_after_advice': signature(final),
                'advice': 'POSIX_FADV_DONTNEED', 'offset': 0, 'length': 0}


def run_once(lockfd, accounting, record, save, current_inputs, finish_fd):
    st = os.fstat(lockfd)
    if (st.st_dev, st.st_ino) != (33, 3849):
        raise RuntimeError('Recovery lock mismatch')
    marker = B / 'recovery-pass-claimed.json'
    with marker.open('x') as f:
        json.dump({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'one_pass_only': True}, f)
    plan = read_plan()
    bound = set(map(str, current_inputs))
    info = {'state': 'started', 'started_ns': time.monotonic_ns(),
            'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'plan_sha256': PLAN_SHA, 'absolute_file_ceiling': FILE_CEILING, 'absolute_byte_ceiling': BYTE_CEILING,
            'lock_device': st.st_dev, 'lock_inode': st.st_ino, 'advised_files': 0, 'advised_bytes': 0,
            'excluded_files': 0, 'excluded_bytes': 0, 'current_bound_input_count': len(bound)}
    record['finite_cache_recovery'] = info
    info['before'] = accounting.sample()
    save()
    reasons = Counter()
    with LOG.open('x+b') as log:
        try:
            for item in plan['entries']:
                row = advise_one(item, set(plan['roots']), bound)
                encoded = (json.dumps(row, separators=(',', ':')) + '\n').encode()
                if log.tell() + len(encoded) > LOG_BOUND:
                    raise RuntimeError('Recovery compact log bound exceeded')
                log.write(encoded)
                if row['status'] == 'advised':
                    info['advised_files'] += 1
                    info['advised_bytes'] += row['bytes']
                else:
                    info['excluded_files'] += 1
                    info['excluded_bytes'] += row['bytes']
                    reasons[row['reason']] += 1
            if info['advised_files'] + info['excluded_files'] != FILE_CEILING or info['advised_bytes'] + info['excluded_bytes'] != BYTE_CEILING:
                raise RuntimeError('Recovery final coverage mismatch')
            info['state'] = 'completed'
        except BaseException as exc:
            info.update(state='failed', failure=repr(exc))
            raise
        finally:
            # Same descriptor: finish, fsync, stream hash and advise the compact log
            # before any after-pass capacity measurement.
            info['log_finish'] = finish_fd(log)
            info['excluded_reasons'] = dict(reasons)
            info['log_finished_ns'] = time.monotonic_ns()
            save()
    info['after'] = accounting.sample()
    info['visible_current_drop_bytes'] = info['before']['nodes'][0]['current'] - info['after']['nodes'][0]['current']
    info['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    info['ended_ns'] = time.monotonic_ns()
    for old, new in zip(info['before']['nodes'], info['after']['nodes'], strict=True):
        if old['oom'] != new['oom'] or old['pids_events'] != new['pids_events'] or old['pids_max'] != new['pids_max']:
            info.update(state='failed', failure='OOM/PID events or limits changed during recovery')
            save()
            raise RuntimeError(info['failure'])
    save()
