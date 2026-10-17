"""Low-memory idle advice using exactly the previously accepted frozen bindings."""
from pathlib import Path
import hashlib
import json
import os
import stat
import time
from shared_preservation import signature, encode, utc

B = Path(__file__).resolve().parent
R = B.parents[1]
PRIOR = R / 'checkpoints/light-eft-batch18-effective-reread-20261017/inputs.jsonl'
PRIOR_SHA = 'de9b5cade136816d74bf21ec30208e802607881dace69e5b2ea641db075ab517'


def run_once(lock, accounting):
    with (B/'bootstrap-claimed.json').open('x') as f:
        json.dump({'utc': utc(), 'one_idle_scope_pass_only': True}, f)
    s = os.fstat(lock.fileno())
    if (s.st_dev, s.st_ino) != (33, 3849):
        raise RuntimeError('Bootstrap advice requires universal lease')
    with PRIOR.open('rb') as f:
        if hashlib.file_digest(f, 'sha256').hexdigest() != PRIOR_SHA:
            raise RuntimeError('Prior accepted inventory bytes changed')
    record = {'started_utc': utc(), 'started_ns': time.monotonic_ns(),
              'authority_commit': 'fb2f9b7773f79a8b6ecb6365aa37d49111233150',
              'authority_inventory_sha256': PRIOR_SHA,
              'operation': 'Idle advice from accepted prior bindings; not new content certification',
              'before': accounting.sample(), 'counts': {}, 'bytes': 0}
    digest = hashlib.sha256()
    try:
        with PRIOR.open() as f:
            for line in f:
                row = json.loads(line)
                scope = row['advice_scope']
                if not scope:
                    continue
                if scope not in ('previously_accepted_evidence_data', 'reviewed_dependency_or_tool_object'):
                    raise RuntimeError('Unreviewed advice scope')
                fd = os.open(row['path'], os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
                with os.fdopen(fd, 'rb') as data:
                    s = os.fstat(data.fileno())
                    if not stat.S_ISREG(s.st_mode) or s.st_mode & 0o111 or signature(s) != row['identity']:
                        raise RuntimeError('Prior verified advice identity changed: '+row['path'])
                    os.posix_fadvise(data.fileno(),0,0,os.POSIX_FADV_DONTNEED)
                    if signature(os.fstat(data.fileno())) != row['identity']:
                        raise RuntimeError('Advice target changed: '+row['path'])
                record['counts'][scope] = record['counts'].get(scope,0)+1
                record['bytes'] += row['bytes']
                digest.update(encode({'path':row['path'],'identity':row['identity']}))
        assert record['counts']=={'previously_accepted_evidence_data':7129,'reviewed_dependency_or_tool_object':66961}
        assert record['bytes']==11790867848
        record['state']='completed'
    except BaseException as exc:
        record.update(state='failed',failure=repr(exc))
        raise
    finally:
        record.update(ended_utc=utc(),ended_ns=time.monotonic_ns(),scope_identity_sha256=digest.hexdigest(),after=accounting.sample())
        record['visible_current_drop_bytes']=record['before']['nodes'][0]['current']-record['after']['nodes'][0]['current']
        (B/'bootstrap-recovery.json').write_text(json.dumps(record,indent=2)+'\n')
    for old,new in zip(record['before']['nodes'],record['after']['nodes'],strict=True):
        if old['oom']!=new['oom'] or old['pids_events']!=new['pids_events']:
            raise RuntimeError('OOM/PID event changed during bootstrap idle advice')
    return record
