"""Finite evidence housekeeping inside the reviewed exclusion lock; no data removal."""
from pathlib import Path
import datetime,hashlib,json,os,stat,time
from pilot_cache_advice import signature
HERE=Path(__file__).resolve().parent
WHITELIST=HERE/'history-whitelist.json'
WHITELIST_SHA='607572c0ca227506b66f9cde20979e1238ccea84437c7876f81311662eac6c0f'
NEW_NAMES={'inputs-before.json','inputs-after.json','hash-advice-before.jsonl','hash-advice-after.jsonl','raw.log','samples.jsonl'}
HISTORY_LOG=HERE/'history-advice.jsonl'

def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def approved_new(path):
    p=Path(path)
    if p.is_symlink():raise RuntimeError('New completed file is a symlink')
    if p==HISTORY_LOG:return p
    if p.parent.parent!=HERE/'evidence' or p.parent.name not in ('compile','resolve','replay') or p.name not in NEW_NAMES:raise RuntimeError('Outside fixed new-file housekeeping scope')
    return p

def finish_fd(f,expected=None):
    f.flush();os.fsync(f.fileno())
    before=os.fstat(f.fileno())
    if not stat.S_ISREG(before.st_mode):raise RuntimeError('Not a regular completed file')
    f.seek(0);value=hashlib.file_digest(f,'sha256').hexdigest();after=os.fstat(f.fileno())
    if signature(before)!=signature(after):raise RuntimeError('Completed file changed during hash')
    if expected is not None and (value!=expected['sha256'] or after.st_size!=expected['bytes']):raise RuntimeError('Expected file hash/size mismatch')
    row={'sha256':value,'bytes':after.st_size,'identity':signature(after),'flushed_fsynced':True,'advice':'POSIX_FADV_DONTNEED','offset':0,'length':0}
    os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
    final=os.fstat(f.fileno());row['identity_after_advice']=signature(final)
    if signature(after)!=signature(final):raise RuntimeError('Completed file changed during advice')
    return row

def complete_open(path,f,record,save):
    path=approved_new(path);key=str(path);entries=record.setdefault('completed_file_housekeeping',{})
    if key in entries:
        if entries[key]['state']=='completed':return entries[key]
        raise RuntimeError('Never retry incomplete housekeeping: '+key)
    entries[key]={'state':'claimed','started_ns':time.monotonic_ns()};save()
    try:
        entries[key].update(finish_fd(f));entries[key].update(state='completed',ended_ns=time.monotonic_ns());save();return entries[key]
    except BaseException as exc:
        entries[key].update(state='failed',failure=repr(exc));save();raise

def complete_one(path,record,save):
    path=approved_new(path);entry=record.get('completed_file_housekeeping',{}).get(str(path))
    if entry:
        if entry['state']=='completed':return entry
        raise RuntimeError('Never retry failed housekeeping')
    fd=os.open(path,os.O_RDWR|os.O_NOFOLLOW|os.O_NONBLOCK)
    with os.fdopen(fd,'r+b') as f:return complete_open(path,f,record,save)

def write_inventory(rows,path,record,save):
    path=approved_new(path)
    with path.open('x+b') as f:
        # Iterative encoding avoids constructing a second whole JSON string.
        for chunk in json.JSONEncoder(indent=2).iterencode(rows):f.write(chunk.encode('utf-8'))
        f.write(b'\n')
        return complete_open(path,f,record,save)

def load_whitelist():
    raw=WHITELIST.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=WHITELIST_SHA:raise RuntimeError('Pinned history whitelist changed')
    plan=json.loads(raw);rows=plan['files'];mapping={row['path']:row for row in rows}
    if len(rows)!=407 or len(mapping)!=407 or sum(x['bytes'] for x in rows)!=183081165:raise RuntimeError('History whitelist count/bytes mismatch')
    return rows,mapping

def advise_historical(row,mapping):
    path=Path(row['path'])
    if mapping.get(str(path))!=row:raise RuntimeError('Not a pinned whitelist member')
    if not path.is_absolute() or '..' in path.parts or any(x.is_symlink() for x in [path,*path.parents]):raise RuntimeError('Noncanonical/symlink historical path')
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
    with os.fdopen(fd,'rb') as f:
        before=os.fstat(f.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_size!=row['bytes']:raise RuntimeError('Historical type/size mismatch')
        value=hashlib.file_digest(f,'sha256').hexdigest();after=os.fstat(f.fileno())
        if signature(before)!=signature(after) or value!=row['sha256']:raise RuntimeError('Historical identity/hash mismatch')
        result={**row,'verified_sha256':value,'identity':signature(after),'advice':'POSIX_FADV_DONTNEED','offset':0,'length':0}
        os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
        final=os.fstat(f.fileno());result['identity_after_advice']=signature(final)
        if signature(after)!=signature(final):raise RuntimeError('Historical identity changed during advice')
    return result

def memory_stat():
    result={}
    for root in ['/sys/fs/cgroup','/sys/fs/cgroup/init']:
        fd=os.open(root+'/memory.stat',os.O_RDONLY|os.O_NOFOLLOW)
        try:result[root]=os.read(fd,65536).decode()
        finally:os.close(fd)
    return result

def run_history_once(lockfd,accounting,record,save):
    lockstat=os.fstat(lockfd)
    if (lockstat.st_dev,lockstat.st_ino)!=(33,3849):raise RuntimeError('Wrong inherited history lock descriptor')
    with (HERE/'history-pass-claimed.json').open('x') as f:json.dump({'utc':utc(),'one_pass_only':True},f)
    rows,mapping=load_whitelist()
    history={'began_utc':utc(),'whitelist_sha256':WHITELIST_SHA,'count':0,'bytes':0,'lock_device':lockstat.st_dev,'lock_inode':lockstat.st_ino,'state':'started'}
    record['history_pass']=history;history['before']=accounting.sample();history['memory_stat_before']=memory_stat();save()
    try:
        with HISTORY_LOG.open('xb') as log:
            for row in rows:
                try:result=advise_historical(row,mapping)
                except BaseException as exc:
                    log.write((json.dumps({'path':row['path'],'error':repr(exc)})+'\n').encode());raise
                log.write((json.dumps(result)+'\n').encode());history['count']+=1;history['bytes']+=row['bytes']
            log.flush();os.fsync(log.fileno())
        complete_one(HISTORY_LOG,record,save)
        history['state']='completed'
    except BaseException as exc:
        history.update(state='failed',failure=repr(exc));raise
    finally:
        if HISTORY_LOG.exists() and str(HISTORY_LOG) not in record.get('completed_file_housekeeping',{}):complete_one(HISTORY_LOG,record,save)
        history['after']=accounting.sample();history['memory_stat_after']=memory_stat();history['ended_utc']=utc()
        history['visible_current_drop_bytes']=history['before']['nodes'][0]['current']-history['after']['nodes'][0]['current'];save()
        for old,new in zip(history['before']['nodes'],history['after']['nodes'],strict=True):
            if old['oom']!=new['oom'] or old['pids_events']!=new['pids_events'] or old['pids_max']!=new['pids_max']:
                history.update(state='failed',failure='OOM/PID limit/event changed during history pass');save();raise RuntimeError(history['failure'])
    if history['count']!=407 or history['bytes']!=183081165:raise RuntimeError('Incomplete history pass')

def admit_after_preflight(evidence,before,stage,lockfd,accounting,record,save,gate):
    order=record.setdefault('preflight_order',[]);order.append('input-verification-completed')
    inv=write_inventory(before,evidence/'inputs-before.json',record,save)
    complete_one(evidence/'hash-advice-before.jsonl',record,save)
    record['inputs_manifest_sha256']=inv['sha256'];order.append('new-preflight-files-fsynced-hashed-advised');save()
    if stage=='compile':
        run_history_once(lockfd,accounting,record,save);order.append('single-history-pass-completed')
    if stage!='replay':raise RuntimeError('Only checker stage authorized for finite recovery')
    import cache_recovery
    cache_recovery.run_once(lockfd,accounting,record,save,[Path(x['path']) for x in before],finish_fd)
    order.append('finite-manifest-recovery-log-fsynced-hashed-advised');save()
    now=accounting.sample();record['admission']=now;order.append('fresh-admission-sampled');save()
    gate(now);order.append('admission-passed');save();return now
