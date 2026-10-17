"""Whole-batch exclusion and immutable-content bindings, independent of Lean."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import stat
import time

LOCK = Path('/tmp/distance-sparsification-single-compiler.lock')


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def signature(s):
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def encode(row):
    return (json.dumps(row, separators=(',', ':')) + '\n').encode()


def inspect(path, spec):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as f:
        a = os.fstat(f.fileno())
        if not stat.S_ISREG(a.st_mode):
            raise RuntimeError('Nonregular bound input: ' + str(path))
        value = hashlib.file_digest(f, 'sha256').hexdigest()
        b = os.fstat(f.fileno())
        if signature(a) != signature(b):
            raise RuntimeError('Input changed while hashing: ' + str(path))
        if spec.get('expected_sha256') and value != spec['expected_sha256']:
            raise RuntimeError('Pinned content changed: ' + str(path))
        if spec.get('expected_identity') and signature(b) != spec['expected_identity']:
            raise RuntimeError('Pinned identity changed: ' + str(path))
        return {'path': str(path), 'bytes': b.st_size, 'sha256': value,
                'identity': signature(b), 'role': spec['role'], 'advice_scope': spec.get('advice_scope')}


class Lease:
    """Never replace/unlink the common inode; release only after kernel ECHILD."""
    def __init__(self, report):
        self.report = Path(report)
        self.record = {}
        self.file = None

    def save(self):
        self.report.write_text(json.dumps(self.record, indent=2) + '\n')

    def __enter__(self):
        self.file = LOCK.open('r+')
        try:
            fcntl.flock(self.file, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BaseException:
            self.file.close()
            raise
        s = os.fstat(self.file.fileno())
        if (s.st_dev, s.st_ino) != (33, 3849):
            self.file.close()
            raise RuntimeError('Universal lock inode changed')
        self.record = {'acquired_utc': utc(), 'acquired_ns': time.monotonic_ns(),
                       'device': s.st_dev, 'inode': s.st_ino, 'fd': self.file.fileno(),
                       'supervisor_pid': os.getpid(), 'state': 'held'}
        self.save()
        return self.file

    def __exit__(self, typ, value, tb):
        # Every production child has already passed its cleanup barrier. Do not
        # unlock if the kernel still has any child, even when /proc looks idle.
        try:
            pid, status = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            self.record['kernel_echild_at_release'] = True
        else:
            self.record.update(state='release-refused', unexpected_waitpid=[pid, status])
            self.save()
            raise RuntimeError('Universal lease release refused: kernel child remains')
        self.record.update(state='release-verified', release_verified_ns=time.monotonic_ns(), release_verified_utc=utc())
        self.save()
        self.file.close()
        self.record.update(state='released', released_ns=time.monotonic_ns(), released_utc=utc())
        self.save()


class FrozenInputs:
    def __init__(self, specs, directory):
        self.specs = {str(Path(k)): v for k, v in sorted(specs.items(), key=lambda x: str(x[0]))}
        self.directory = Path(directory)
        self.rows = {}
        self.digest = None
        self.before_complete = False

    def freeze(self):
        digest = hashlib.sha256()
        path = self.directory / 'inputs.jsonl'
        with path.open('xb') as out:
            for name, spec in self.specs.items():
                row = inspect(name, spec)
                self.rows[name] = row
                data = encode(row)
                out.write(data)
                digest.update(data)
            out.flush()
            os.fsync(out.fileno())
        self.digest = digest.hexdigest()
        self.before_complete = True
        return {'path': str(path), 'sha256': self.digest, 'rows': len(self.rows),
                'bytes': path.stat().st_size, 'completed_utc': utc()}

    def identities(self):
        for name, row in self.rows.items():
            s = os.lstat(name)
            if not stat.S_ISREG(s.st_mode) or signature(s) != row['identity']:
                raise RuntimeError('Between-child input identity changed: ' + name)
        if not self.before_complete or len(self.rows) != len(self.specs):
            raise RuntimeError('Canonical inventory incomplete')

    def final_verify(self):
        started = time.monotonic_ns()
        digest = hashlib.sha256()
        changes = []
        checked = 0
        for name, spec in self.specs.items():
            try:
                row = inspect(name, spec)
                digest.update(encode(row))
                if self.rows.get(name) != row:
                    changes.append({'path': name, 'reason': 'Content/identity differs from canonical baseline', 'observed': row})
            except Exception as exc:
                changes.append({'path': name, 'error': repr(exc)})
            checked += 1
        good = self.before_complete and not changes and digest.hexdigest() == self.digest
        result = {'started_ns': started, 'ended_ns': time.monotonic_ns(), 'utc': utc(),
                  'all_paths_attempted': checked == len(self.specs), 'paths_checked': checked,
                  'before_complete': self.before_complete, 'before_sha256': self.digest,
                  'after_stream_sha256': digest.hexdigest(), 'matching': good, 'changes': changes}
        (self.directory / 'final-content-verification.json').write_text(json.dumps(result, indent=2) + '\n')
        return result

    def advise_verified(self, accounting, label):
        """No content reread: only the exact already-hashed eligible bindings."""
        before = accounting.sample()
        counts = {}
        total = 0
        scope_digest = hashlib.sha256()
        result = {'label': label, 'started_utc': utc(), 'started_ns': time.monotonic_ns(), 'before': before}
        try:
            for name, row in self.rows.items():
                scope = row['advice_scope']
                if not scope:
                    continue
                fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
                with os.fdopen(fd, 'rb') as f:
                    s = os.fstat(f.fileno())
                    if not stat.S_ISREG(s.st_mode) or s.st_mode & 0o111 or signature(s) != row['identity']:
                        raise RuntimeError('Verified advice identity/mode changed: ' + name)
                    os.posix_fadvise(f.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
                    if signature(os.fstat(f.fileno())) != row['identity']:
                        raise RuntimeError('Input changed during verified advice: ' + name)
                counts[scope] = counts.get(scope, 0) + 1
                total += row['bytes']
                scope_digest.update(encode({'path': name, 'identity': row['identity']}))
            result['state'] = 'completed'
        except BaseException as exc:
            result.update(state='failed', failure=repr(exc))
            raise
        finally:
            result.update(counts=counts, bytes=total, scope_identity_sha256=scope_digest.hexdigest(),
                          ended_ns=time.monotonic_ns(), ended_utc=utc(), after=accounting.sample())
            result['visible_current_drop_bytes'] = before['nodes'][0]['current'] - result['after']['nodes'][0]['current']
            with (self.directory / 'cache-advice.jsonl').open('a') as log:
                log.write(json.dumps(result, separators=(',', ':')) + '\n')
                log.flush()
                os.fsync(log.fileno())
        return result
