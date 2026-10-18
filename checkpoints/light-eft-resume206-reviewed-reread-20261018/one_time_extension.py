"""One exact recorded archive/data extension; no extraction or broader search."""
from pathlib import Path
import fcntl
import hashlib
import json
import os
import stat
import time
from finalized_scope import selected as legacy_selected, ScopedFrozenInputs
from shared_preservation import signature, encode, utc

ARCHIVE = 'approved_archive_extension'
DATA = 'approved_finalized_extension'
NEW = {ARCHIVE, DATA}
LEGACY = {'reviewed_finalized_batch_data', 'reviewed_dependency_or_tool_object', 'previously_accepted_evidence_data'}
TOP = {'inputs.jsonl', 'output-records.jsonl', 'cache-advice.jsonl', 'result-reconciliation.json',
       'module-status.json', 'source-toolchain-object-hashes.json', 'publication-checks.json'}
REPLAY = {'hash-advice-before.jsonl', 'hash-advice-after.jsonl', 'inputs-before.json', 'inputs-after.json', 'receipt.json', 'samples.jsonl', 'raw.log'}
CHUNKS = {'evidence-replay-hash-advice-before-jsonl', 'evidence-replay-hash-advice-after-jsonl', 'evidence-replay-inputs-before-json'}


def authority(root, binding):
    raw = (root / binding['path']).read_bytes()
    if len(raw) != binding['bytes'] or hashlib.sha256(raw).hexdigest() != binding['sha256']:
        raise RuntimeError('Recorded scope authority changed: ' + binding['path'])
    return json.loads(raw)


def selected(root, plan):
    rows = legacy_selected(root, plan)
    for row in rows.values():
        row['scope'] = 'reviewed_finalized_batch_data'
    extension = {}
    def add(path, row, scope):
        path = Path(path)
        if str(path) in rows or str(path) in extension:
            raise RuntimeError('Duplicate approved extension path')
        for parent in path.parents:
            if parent.is_symlink():
                raise RuntimeError('Symlink scope parent')
        info = os.lstat(path)
        if not stat.S_ISREG(info.st_mode) or info.st_mode & 0o111:
            raise RuntimeError('Nonregular/executable/symlink extension target: ' + str(path))
        if info.st_size != row['bytes']:
            raise RuntimeError('Recorded scope size changed: ' + str(path))
        extension[str(path)] = {'path': str(path), 'bytes': row['bytes'], 'sha256': row['sha256'],
                                'scope': scope, 'expected_identity': signature(info)}
    archives = authority(root, plan['new_archive_authorities'][0])['archives']
    if len(archives) != 3808:
        raise RuntimeError('Archive inventory count changed')
    for row in archives:
        path = Path(row['local_archive'])
        if path.parent != Path('/workspace/cache/mathlib') or path.name != row['cache_key'] + '.ltar':
            raise RuntimeError('Archive outside exact recorded cache paths')
        add(path, row, ARCHIVE)
    tool = authority(root, plan['new_archive_authorities'][1])['official_archive']
    if tool['path'] != '/workspace/toolchains/lean.tar.zst':
        raise RuntimeError('Unexpected toolchain archive path')
    add(tool['path'], tool, ARCHIVE)
    counts_by_checkpoint = {}
    for binding in plan['new_data_manifests']:
        manifest_path = root / binding['path']
        directory = manifest_path.parent.name
        count = 0
        for row in authority(root, binding):
            rel = Path(row['path'])
            parts = rel.parts
            allowed = row['path'] in TOP
            if directory == 'light-eft-finitelaw-finite-recovery-20261017':
                allowed |= len(parts) == 3 and parts[:2] == ('evidence', 'replay') and parts[-1] in REPLAY
                allowed |= len(parts) == 3 and parts[0] == 'chunks' and parts[1] in CHUNKS and parts[-1].startswith('part-') and parts[-1].endswith('.txt')
            else:
                allowed |= len(parts) == 3 and parts[0] == 'attempts' and parts[-1] in {'receipt.json', 'samples.jsonl', 'raw.log'}
            if not allowed:
                continue
            if rel.is_absolute() or '..' in parts or '.' in parts:
                raise RuntimeError('Noncanonical finalized-data path')
            add(manifest_path.parent / rel, row, DATA)
            count += 1
        if count != binding['selected_file_count']:
            raise RuntimeError('Checkpoint scope count differs from authorization')
        counts_by_checkpoint[directory] = count
    archive_rows = [row for row in extension.values() if row['scope'] == ARCHIVE]
    data_rows = [row for row in extension.values() if row['scope'] == DATA]
    if len(archive_rows) != 3809 or sum(row['bytes'] for row in archive_rows) != 818684031:
        raise RuntimeError('Archive scope ceiling differs')
    if len(data_rows) != 708 or sum(row['bytes'] for row in data_rows) != 385582329:
        raise RuntimeError('Finalized-data scope ceiling differs')
    if len(extension) != 4517 or sum(row['bytes'] for row in extension.values()) != 1204266360:
        raise RuntimeError('Combined extension ceiling differs')
    return rows | extension


def hash_then_advise(path, row):
    for parent in path.parents:
        if parent.is_symlink():
            raise RuntimeError('Symlink extension parent')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as handle:
        before = os.fstat(handle.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_mode & 0o111 or signature(before) != row['identity']:
            raise RuntimeError('Approved extension identity/mode changed')
        digest = hashlib.file_digest(handle, 'sha256').hexdigest()
        after = os.fstat(handle.fileno())
        if digest != row['sha256'] or after.st_size != row['bytes'] or signature(after) != row['identity'] or signature(os.lstat(path)) != row['identity']:
            raise RuntimeError('Approved extension changed during recorded-binding hash')
        os.posix_fadvise(handle.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        if signature(os.fstat(handle.fileno())) != row['identity'] or signature(os.lstat(path)) != row['identity']:
            raise RuntimeError('Approved extension changed during same-descriptor advice')


class ExtendedFrozenInputs(ScopedFrozenInputs):
    """Full before/after verification unchanged; only one new-scope advice pass.

    Initial full preservation hashes A/B without advising them. The one finite
    hash-then-advice pass follows, before the first 5 GiB admission. Later ordinary
    advice excludes A/B entirely and reuses only the previously approved scopes.
    """
    def advise_once_extension(self, accounting, label):
        with (self.directory / 'extension-pass-claimed.json').open('x') as handle:
            json.dump({'utc': utc(), 'one_pass_only': True}, handle)
        return self._pass(accounting, label, True)

    def advise_verified(self, accounting, label):
        return self._pass(accounting, label, False)

    def _pass(self, accounting, label, extension):
        info = os.fstat(self.lock.fileno())
        if not self.before_complete or (info.st_dev, info.st_ino) != (33, 3849):
            raise RuntimeError('Verified universal lease required for advice')
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        record = {'label': label, 'mode': 'one-time-extension' if extension else 'ordinary-legacy-only',
                  'started_utc': utc(), 'started_ns': time.monotonic_ns(), 'before': accounting.sample()}
        counts = {}
        byte_counts = {}
        total = 0
        scope_digest = hashlib.sha256()
        extension_log = (self.directory / 'one-time-extension-verified.jsonl').open('x') if extension else None
        try:
            for name, row in self.rows.items():
                scope = row['advice_scope']
                if scope is None or scope in NEW and not extension:
                    continue
                if scope not in LEGACY | NEW:
                    raise RuntimeError('Unexpected advice category')
                if scope in NEW:
                    hash_then_advise(Path(name), row)
                    extension_log.write(encode(row).decode())
                else:
                    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
                    with os.fdopen(fd, 'rb') as handle:
                        observed = os.fstat(handle.fileno())
                        if not stat.S_ISREG(observed.st_mode) or observed.st_mode & 0o111 or signature(observed) != row['identity']:
                            raise RuntimeError('Previously verified ordinary advice target changed')
                        os.posix_fadvise(handle.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
                        if signature(os.fstat(handle.fileno())) != row['identity']:
                            raise RuntimeError('Ordinary advice target changed')
                counts[scope] = counts.get(scope, 0) + 1
                byte_counts[scope] = byte_counts.get(scope, 0) + row['bytes']
                total += row['bytes']
                scope_digest.update(encode({'path': name, 'identity': row['identity']}))
            if extension:
                if counts.get(ARCHIVE) != 3809 or byte_counts.get(ARCHIVE) != 818684031 or counts.get(DATA) != 708 or byte_counts.get(DATA) != 385582329:
                    raise RuntimeError('Incomplete finite extension pass')
                extension_log.flush()
                os.fsync(extension_log.fileno())
            record['after'] = accounting.sample()
            for before, after in zip(record['before']['nodes'], record['after']['nodes'], strict=True):
                if before['oom'] != after['oom'] or before['pids_events'] != after['pids_events']:
                    raise RuntimeError('OOM/PID event changed during scoped idle advice')
            record['state'] = 'completed'
        except BaseException as exc:
            record.update(state='failed', failure=repr(exc))
            raise
        finally:
            if extension_log:
                extension_log.close()
            record.update(counts=counts, bytes_by_scope=byte_counts, bytes=total, scope_identity_sha256=scope_digest.hexdigest(),
                          ended_utc=utc(), ended_ns=time.monotonic_ns(), after=record.get('after') or accounting.sample(), nominal_bytes_not_credited_as_reclaimed=True)
            record['visible_current_drop_bytes'] = record['before']['nodes'][0]['current'] - record['after']['nodes'][0]['current']
            with (self.directory / 'cache-advice.jsonl').open('a') as handle:
                handle.write(json.dumps(record, separators=(',', ':')) + '\n')
                handle.flush()
                os.fsync(handle.fileno())
            if extension:
                (self.directory / 'one-time-cache-advice.json').write_text(json.dumps(record, indent=2) + '\n')
        return record
