"""Audit-only output checks. Source-directed limits are not a filesystem quota."""
from pathlib import Path
import hashlib, os, shutil, stat

FILE_LIMIT = 64 * 1024**2
SOURCE_BUDGET = 5 * FILE_LIMIT  # Four fixed source files and raw stdout/stderr.
DECISION_LIMIT = 16 * 1024**2
DISK_FLOOR = 2 * 1024**3
OUTPUTS = ('actual-owner-inventory.tsv', 'recursive-dependencies.tsv',
           'import-closure-loaded.txt', 'strict-violations.txt')


def inspect_outputs(spec, complete=False):
    work = Path(spec['work']); ci = work/'ci-evidence'
    for name, expected in [(work, spec['work_identity']), (ci, spec['ci_identity'])]:
        s = name.lstat()
        if not stat.S_ISDIR(s.st_mode) or [s.st_dev, s.st_ino] != expected:
            raise RuntimeError('Fresh audit directory identity changed: '+str(name))
    allowed = {ci/name for name in OUTPUTS}
    for p in work.rglob('*'):
        s = p.lstat()
        if p == ci and stat.S_ISDIR(s.st_mode): continue
        if p not in allowed or not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
            raise RuntimeError('Unexpected/nonregular audit working-directory entry: '+str(p))
    observed = []; total = 0
    paths = list(sorted(allowed))+[Path(spec['raw'])]
    for p in paths:
        try: s = p.lstat()
        except FileNotFoundError:
            if complete: raise RuntimeError('Missing fresh audit output: '+str(p))
            continue
        if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
            raise RuntimeError('Nonregular/linked audit output: '+str(p))
        if s.st_size > FILE_LIMIT:
            raise RuntimeError('Audit file exceeds64MiB: '+str(p))
        if complete and s.st_mtime_ns < spec['created_wall_ns']:
            raise RuntimeError('Stale audit output timestamp: '+str(p))
        total += s.st_size
        observed.append({'path':str(p), 'bytes':s.st_size})
    if total > SOURCE_BUDGET:
        raise RuntimeError('Four audit outputs plus raw output exceed320MiB')
    return {'files':observed, 'source_directed_bytes':total,
            'source_directed_limit':SOURCE_BUDGET,
            'qualification':'Pinned source has four fixed writes; per-file RLIMIT_FSIZE and membership checks, not a disk quota'}


def runtime_errors(record, preexec=False):
    spec = record['audit_output_budget']
    inspect_outputs(spec)
    if preexec and shutil.disk_usage(spec['work']).free <= DISK_FLOOR:
        return ['Fresh preexec disk headroom must exceed2GiB']
    return []


def bind_outputs(spec):
    result = inspect_outputs(spec, complete=True)
    for row in result['files']:
        p = Path(row['path'])
        fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(fd,'rb') as f:
            a = os.fstat(f.fileno())
            if not stat.S_ISREG(a.st_mode): raise RuntimeError('Nonregular output')
            os.fsync(f.fileno())
            row['sha256'] = hashlib.file_digest(f,'sha256').hexdigest()
            b = os.fstat(f.fileno())
            sig = lambda s: [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
            if sig(a) != sig(b) or sig(b) != sig(p.lstat()):
                raise RuntimeError('Completed audit output changed while binding')
            row['identity'] = sig(b)
    return result
