"""One exact 12-file historical-evidence advice pass. Never expands recursively."""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,stat,time,traceback
import pilot_runner as p
from pilot_accounting import VisibleAccounting
from pilot_cache_advice import signature
BASE=Path(__file__).resolve().parent
BINDINGS=BASE/'historical-files.json'
BINDING_SHA='b630b06998ee1c5958c8d53d46f306b5aa76169549ccfdb3b5511d78c3b55dad'

def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(record):
    temp=BASE/'advice-result.tmp';temp.write_text(json.dumps(record,indent=2)+'\n');temp.replace(BASE/'advice-result.json')
def memory_stat():
    values={}
    for root in ['/sys/fs/cgroup','/sys/fs/cgroup/init']:
        fd=os.open(root+'/memory.stat',os.O_RDONLY|os.O_NOFOLLOW)
        try:values[root]=os.read(fd,65536).decode()
        finally:os.close(fd)
    return values

def run_once():
    with (BASE/'advice-claimed.json').open('x') as f:json.dump({'one_pass_only':True,'utc':stamp()},f)
    raw=BINDINGS.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=BINDING_SHA:raise RuntimeError('Fixed advice bindings changed')
    plan=json.loads(raw);rows=plan['files']
    if len(rows)!=12 or len({r['path'] for r in rows})!=12 or sum(r['bytes'] for r in rows)!=302254496:raise RuntimeError('Not exact 12-file plan')
    record={'scope':'ONE_EXACT_HISTORICAL_12_FILE_ADVICE_PASS','began_utc':stamp(),'bindings_sha256':BINDING_SHA,'files':[],'state':'created','advice_calls':0,'bytes_advised':0}
    save(record)
    with p.LOCK.open('r+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(lock.fileno())
        if (st.st_dev,st.st_ino)!=(33,3849):raise RuntimeError('Universal lock identity mismatch')
        record['lock']={'device':st.st_dev,'inode':st.st_ino,'fd':lock.fileno()}
        accounting=VisibleAccounting()
        record['before']=accounting.sample();record['memory_stat_before']=memory_stat();save(record)
        try:
            for proc in Path('/proc').glob('[0-9]*'):
                try:
                    if (proc/'comm').read_text().strip() in ('lean','lake','leanchecker','leantar') and 'Z' not in (proc/'stat').read_text().rsplit(')',1)[1].split()[0]:raise RuntimeError('Other compiler/checker/extractor active')
                except (FileNotFoundError,ProcessLookupError):continue
            for row in rows:
                path=Path(row['path'])
                if not path.is_absolute() or '..' in path.parts or any(q.is_symlink() for q in [path,*path.parents]):raise RuntimeError('Symlink/noncanonical fixed path')
                event={**row,'started_ns':time.monotonic_ns(),'advised':False};record['files'].append(event);save(record)
                fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
                with os.fdopen(fd,'rb') as f:
                    before=os.fstat(f.fileno())
                    if not stat.S_ISREG(before.st_mode) or before.st_size!=row['bytes']:raise RuntimeError('Historical file type/size mismatch')
                    value=hashlib.file_digest(f,'sha256').hexdigest();after=os.fstat(f.fileno())
                    if signature(before)!=signature(after) or value!=row['sha256']:raise RuntimeError('Historical file identity/hash mismatch')
                    event.update(verified_sha256=value,identity=signature(after),advice='POSIX_FADV_DONTNEED',offset=0,length=0)
                    os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
                    event['advised']=True;record['advice_calls']+=1;record['bytes_advised']+=before.st_size
                    final=os.fstat(f.fileno());event['identity_after_advice']=signature(final)
                    if signature(after)!=signature(final):raise RuntimeError('Historical identity changed during advice')
                save(record)
            record['state']='completed'
        except BaseException as exc:
            record['state']='failed';record['failure']=repr(exc);traceback.print_exc();raise
        finally:
            record['after']=accounting.sample();record['memory_stat_after']=memory_stat();record['ended_utc']=stamp()
            record['visible_current_drop_bytes']=record['before']['nodes'][0]['current']-record['after']['nodes'][0]['current']
            record['visible_headroom_gain_bytes']=record['after']['headroom']-record['before']['headroom']
            record['interpretation']='Observed accounting changes; successful advice is not proof of exclusive causal attribution or full reclamation.'
            save(record)
    if record['advice_calls']!=12 or record['bytes_advised']!=302254496:raise RuntimeError('Advice pass incomplete')
    return record
