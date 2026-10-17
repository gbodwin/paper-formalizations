"""Advisory release only after same-descriptor identity and content verification.
No deletion, truncation, global drop_caches, sync, or advice to executable/library files.
"""
from pathlib import Path
import hashlib,json,os,stat,time
PACKAGE_ROOT=Path('/workspace/paper-formalizations/.lake/packages')
INVENTORY=Path('/workspace/light-eft-verification/checkpoints/light-eft-bounded-import-result-20261017/evidence/inputs-before.json')
INVENTORY_SHA='0e5ac21fd8217f2ae19be1f5be7e23e080b8c67387efead248fc384ad22053ba'
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir')

def signature(s):return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def eligible(path):
    p=Path(path)
    if not p.is_absolute() or '..' in p.parts:return False
    try:parts=p.relative_to(PACKAGE_ROOT).parts
    except ValueError:return False
    if len(parts)<2:return False
    tail=parts[1:]
    if tail[:4]==('.lake','build','lib','lean'):
        return len(tail)>4 and str(p).endswith(SUFFIXES)
    return p.suffix=='.lean' and all(not x.startswith('.') for x in tail)

def load_inventory():
    with INVENTORY.open('rb') as f:
        if hashlib.file_digest(f,'sha256').hexdigest()!=INVENTORY_SHA:raise RuntimeError('Historical inventory hash mismatch')
    rows=json.loads(INVENTORY.read_text())
    if len({x['path'] for x in rows})!=len(rows):raise RuntimeError('Duplicate inventory path')
    return {x['path']:x for x in rows}

def hash_input(path,expected=None,advice_log=None):
    p=Path(path)
    # An expected row is authority to compare, never authority to broaden eligibility.
    event={'path':str(p),'monotonic_ns':time.monotonic_ns(),'advised':False}
    try:
        fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
        with os.fdopen(fd,'rb') as f:
            before=os.fstat(f.fileno())
            if not stat.S_ISREG(before.st_mode):raise RuntimeError('Not a regular input')
            value=hashlib.file_digest(f,'sha256').hexdigest();after=os.fstat(f.fileno())
            if signature(before)!=signature(after):raise RuntimeError('Input changed during hashing')
            row={'path':str(p),'sha256':value,'bytes':after.st_size,'identity':signature(after)}
            if expected is not None and row!=expected:raise RuntimeError('Inventory identity/hash mismatch')
            if advice_log is not None and eligible(p):
                if expected is None:raise RuntimeError('Eligible advice requires inventoried identity/hash')
                if before.st_mode & 0o111:
                    event['excluded']='executable mode; no advice'
                else:
                    event.update(identity=signature(after),sha256=value,bytes=after.st_size,advice='POSIX_FADV_DONTNEED',offset=0,length=0)
                    os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
                    event['advised']=True
                    if signature(os.fstat(f.fileno()))!=signature(after):raise RuntimeError('Input changed during advice')
                    event['reclaimed_bytes']=None
            elif advice_log is not None:event['excluded']='outside dependency source/object allowlist'
        return row
    except BaseException as e:
        event['error']=repr(e);raise
    finally:
        if advice_log is not None:
            with Path(advice_log).open('a') as f:f.write(json.dumps(event)+'\n');f.flush()
