"""Exactly the two authorized manifest subsets; no filesystem inventory hunt."""
from pathlib import Path
import fcntl
import hashlib
import json
import os
import stat
import time
from shared_preservation import FrozenInputs, inspect, signature, encode, utc
from pilot_accounting import VisibleAccounting

TOP = {'inputs.jsonl', 'output-records.jsonl', 'cache-advice.jsonl',
       'result-reconciliation.json', 'module-status.json',
       'source-toolchain-object-hashes.json', 'publication-checks.json'}
SCOPE = 'reviewed_finalized_batch_data'


def selected(root, plan):
    rows = {}
    for authority in plan['expanded_advice_manifests']:
        path = root / authority['path']
        raw = path.read_bytes()
        if len(raw) != authority['bytes'] or hashlib.sha256(raw).hexdigest() != authority['sha256']:
            raise RuntimeError('Accepted manifest changed: ' + str(path))
        for row in json.loads(raw):
            rel = Path(row['path'])
            parts = rel.parts
            allowed = row['path'] in TOP or (len(parts) == 3 and parts[0] == 'attempts' and parts[2] in {'receipt.json', 'samples.jsonl', 'raw.log'})
            if not allowed:
                continue
            if rel.is_absolute() or '..' in parts or '.' in parts:
                raise RuntimeError('Noncanonical manifest path')
            target = path.parent / rel
            if str(target) in rows:
                raise RuntimeError('Duplicate scope path')
            rows[str(target)] = {'path': str(target), 'bytes': row['bytes'], 'sha256': row['sha256']}
    if len(rows) != plan['expanded_advice_file_ceiling'] or len(rows) != 623:
        raise RuntimeError('Expanded scope count differs from exact authorized ceiling')
    if sum(row['bytes'] for row in rows.values()) != plan['expanded_advice_byte_ceiling'] or plan['expanded_advice_byte_ceiling'] != 234041133:
        raise RuntimeError('Expanded scope byte count differs from exact authorized ceiling')
    return rows


def inspect_and_advise(path, spec):
    # Reject symlink parents as well as the final entry. Never follow an
    # executable, object payload, code or unlisted filesystem path.
    for parent in path.parents:
        if parent.is_symlink():
            raise RuntimeError('Symlink parent in finalized scope: ' + str(parent))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as handle:
        before = os.fstat(handle.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_mode & 0o111:
            raise RuntimeError('Nonregular/executable finalized data: ' + str(path))
        value = hashlib.file_digest(handle, 'sha256').hexdigest()
        after = os.fstat(handle.fileno())
        if signature(before) != signature(after) or signature(os.lstat(path)) != signature(after):
            raise RuntimeError('Finalized file changed during streaming hash')
        if value != spec['expected_sha256'] or after.st_size != spec['expected_bytes']:
            raise RuntimeError('Finalized file differs from accepted manifest: ' + str(path))
        os.posix_fadvise(handle.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        if signature(os.fstat(handle.fileno())) != signature(after) or signature(os.lstat(path)) != signature(after):
            raise RuntimeError('Finalized file changed during same-FD advice')
        return {'path': str(path), 'bytes': after.st_size, 'sha256': value,
                'identity': signature(after), 'role': spec['role'], 'advice_scope': SCOPE}


class ScopedFrozenInputs(FrozenInputs):
    """Original preservation semantics with same-FD advice on these data only.

    Subsequent ordinary advise_verified uses the resulting hashed identities.
    Final verification remains the original full content pass, without advice.
    """
    def freeze(self):
        with_fd = os.fstat(self.lock.fileno())
        if (with_fd.st_dev, with_fd.st_ino) != (33, 3849):
            raise RuntimeError('Expanded initial advice requires universal lease')
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        accounting = VisibleAccounting()
        record = {'operation': 'Same-FD manifest hash/advice integrated in the full initial preservation pass',
                  'started_utc': utc(), 'started_ns': time.monotonic_ns(),
                  'before': accounting.sample(), 'counts': {}, 'bytes': 0}
        digest = hashlib.sha256()
        scope_digest = hashlib.sha256()
        path = self.directory / 'inputs.jsonl'
        try:
            with path.open('xb') as out, (self.directory / 'expanded-scope-verified.jsonl').open('x') as scope_log:
                for name, spec in self.specs.items():
                    row = inspect_and_advise(Path(name), spec) if spec.get('advice_scope') == SCOPE else inspect(name, spec)
                    self.rows[name] = row
                    data = encode(row)
                    out.write(data)
                    digest.update(data)
                    if row['advice_scope'] == SCOPE:
                        scope_log.write(data.decode())
                        record['counts'][SCOPE] = record['counts'].get(SCOPE, 0) + 1
                        record['bytes'] += row['bytes']
                        scope_digest.update(encode({'path': name, 'identity': row['identity']}))
                for handle in (out, scope_log):
                    handle.flush()
                    os.fsync(handle.fileno())
            if record['counts'] != {SCOPE: 623} or record['bytes'] != 234041133:
                raise RuntimeError('Incomplete expanded scope in full initial preservation')
            self.digest = digest.hexdigest()
            self.before_complete = True
            record['state'] = 'completed'
        except BaseException as exc:
            record.update(state='failed', failure=repr(exc))
            raise
        finally:
            record.update(ended_utc=utc(), ended_ns=time.monotonic_ns(), after=accounting.sample(), scope_identity_sha256=scope_digest.hexdigest())
            record['visible_current_drop_bytes'] = record['before']['nodes'][0]['current'] - record['after']['nodes'][0]['current']
            record['capacity_qualification'] = 'Whole initial-pass counter difference includes other input reads; nominal advised bytes are not credited as reclaimed. Each child uses actual fresh admission.'
            (self.directory / 'expanded-scope-initial.json').write_text(json.dumps(record, indent=2) + '\n')
        for before, after in zip(record['before']['nodes'], record['after']['nodes'], strict=True):
            if before['oom'] != after['oom'] or before['pids_events'] != after['pids_events']:
                self.before_complete = False
                record.update(state='failed', failure='OOM/PID event changed during full initial preservation/advice')
                (self.directory / 'expanded-scope-initial.json').write_text(json.dumps(record, indent=2) + '\n')
                raise RuntimeError('OOM/PID event changed during full initial preservation/advice')
        return {'path': str(path), 'sha256': self.digest, 'rows': len(self.rows),
                'bytes': path.stat().st_size, 'completed_utc': utc()}
