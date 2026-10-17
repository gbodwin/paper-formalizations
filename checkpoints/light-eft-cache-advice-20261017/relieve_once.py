"""One authorized bounded advisory pass. No compiler, deletion or global cache action."""
from pathlib import Path
import datetime,fcntl,json,os,stat,time,traceback,uuid
from pilot_cache_advice import hash_input,load_inventory
from pilot_accounting import VisibleAccounting
HERE=Path(__file__).resolve().parent
LOCK=Path('/tmp/distance-sparsification-single-compiler.lock')
MAX_FILES=512
MAX_BYTES=1024**3

def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def processes():
    rows=[]
    for directory in Path('/proc').glob('[0-9]*'):
        try:
            name=(directory/'comm').read_text().strip();raw=(directory/'status').read_text()
            fields=dict(line.split(':',1) for line in raw.splitlines() if ':' in line)
            rows.append({'pid':int(directory.name),'comm':name,'state':fields['State'].strip(),'rss_bytes':int(fields.get('VmRSS','0 kB').split()[0])*1024})
        except (FileNotFoundError,ProcessLookupError):continue
        except OSError as e:rows.append({'pid':int(directory.name),'error':repr(e)})
    return rows

def assert_idle(rows):
    if any('error' in r for r in rows):raise RuntimeError('Unreadable process observation')
    if any(r['comm'] in ('lean','lake','leanchecker','leantar') and not r['state'].startswith('Z') for r in rows):raise RuntimeError('Active compiler/checker/extractor')

def snapshot(account):
    s=account.sample();s['utc']=now();s['process_rss']=processes()
    for node in s['nodes']:
        fd=os.open(Path(node['path'])/'memory.stat',os.O_RDONLY|os.O_NOFOLLOW)
        try:raw=os.read(fd,65536).decode()
        finally:os.close(fd)
        node['memory_stat_raw']=raw;node['memory_stat']={k:int(v) for k,v in (line.split() for line in raw.splitlines())}
        for key in ('file','anon','shmem','file_dirty','file_writeback','inactive_file','active_file','slab_reclaimable'):
            if key not in node['memory_stat']:raise RuntimeError('Missing required memory.stat: '+key)
    return s

def main():
    out=HERE/'evidence/one-advisory-pass';out.mkdir(exist_ok=False)
    receipt={'attempt_id':uuid.uuid4().hex,'status':'created','start_utc':now(),'pid':os.getpid(),'bounds':{'max_files':MAX_FILES,'max_bytes':MAX_BYTES},'files_completed':0,'bytes_advised':0,'no_compiler':True}
    def save():(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    save()
    with LOCK.open('r+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(lock.fileno())
        receipt['lock']={'device':st.st_dev,'inode':st.st_ino,'fd':lock.fileno(),'acquired_utc':now()};save()
        account=VisibleAccounting()
        try:
            inventory=load_inventory()
            mapping=json.loads((HERE.parent/'light-eft-provenance-fixes-20261017/evidence/dependency-map.json').read_text())
            used={r['module'] for r in mapping['modules']};prefix='/workspace/paper-formalizations/.lake/packages/mathlib/.lake/build/lib/lean/'
            candidates=[r for r in inventory.values() if r['path'].startswith(prefix) and r['path'].endswith('.olean') and r['path'][len(prefix):-6].replace('/','.') not in used]
            selected=[];total=0
            for row in sorted(candidates,key=lambda r:(-r['bytes'],r['path'])):
                if len(selected)>=MAX_FILES:break
                if total+row['bytes']<=MAX_BYTES:selected.append(row);total+=row['bytes']
            (out/'selection.json').write_text(json.dumps({'criterion':'Mathlib primary objects outside frozen 3808-module project dependency map; descending size then path; no expansion','files':selected,'bytes':total},indent=2)+'\n')
            before=snapshot(account);assert_idle(before['process_rss']);(out/'before.json').write_text(json.dumps(before,indent=2)+'\n')
            receipt['status']='single-pass-running';save()
            for row in selected:
                assert_idle(processes())
                # Same descriptor: hash+identity comparison, then advice, then metadata check.
                hash_input(row['path'],row,out/'file-advice.jsonl')
                receipt['files_completed']+=1;receipt['bytes_advised']+=row['bytes']
                current=account.sample()
                if any(a['oom']!=b['oom'] for a,b in zip(current['nodes'],before['nodes'],strict=True)):raise RuntimeError('OOM event delta; stop bounded pass')
            receipt['status']='pass-completed'
        except BaseException as e:
            receipt['status']='stopped-on-error';receipt['error']=repr(e);traceback.print_exc()
        finally:
            try:
                after=snapshot(account);assert_idle(after['process_rss']);(out/'after.json').write_text(json.dumps(after,indent=2)+'\n')
                receipt['terminal_compilers_idle']=True
            except BaseException as e:receipt['after_error']=repr(e)
            receipt['end_utc']=now();receipt['advice_is_not_reclamation_proof']=True;save()
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
