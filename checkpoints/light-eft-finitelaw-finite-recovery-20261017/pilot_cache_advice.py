"""Advisory release only after same-descriptor identity and content verification.
No deletion, truncation, global drop_caches, sync, or advice to executable/library files.
"""
from pathlib import Path
import hashlib,json,os,stat,time
PACKAGE_ROOT=Path('/workspace/paper-formalizations/.lake/packages')
INVENTORY=Path('/workspace/light-eft-verification/checkpoints/light-eft-bounded-import-result-20261017/evidence/inputs-before.json')
INVENTORY_SHA='0e5ac21fd8217f2ae19be1f5be7e23e080b8c67387efead248fc384ad22053ba'
TOOL_OBJECTS=Path(__file__).resolve().parent/'toolchain-object-advice.json'
TOOL_OBJECTS_SHA='ac8ff793992fec47cbac50629be8e3835b6f81328804b4662a4d6a94e60b65af'
TOOL_ADVICE={}
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir')

def signature(s):return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def eligible(path):
    p=Path(path)
    if not p.is_absolute() or '..' in p.parts:return False
    if str(p) in TOOL_ADVICE:return str(p).endswith(SUFFIXES) and str(p).startswith('/workspace/toolchains/lean-4.34.0-linux/lib/lean/')
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
    inventory={x['path']:x for x in rows}
    tool_raw=TOOL_OBJECTS.read_bytes()
    if hashlib.sha256(tool_raw).hexdigest()!=TOOL_OBJECTS_SHA:raise RuntimeError('Toolchain advice whitelist changed')
    tool=json.loads(tool_raw)['files']
    if len(tool)!=12594 or len({x['path'] for x in tool})!=12594 or sum(x['bytes'] for x in tool)!=2212380925:raise RuntimeError('Toolchain advice count/bytes mismatch')
    if any(inventory.get(x['path'])!=x for x in tool):raise RuntimeError('Toolchain advice exceeds original inventory authority')
    TOOL_ADVICE.clear();TOOL_ADVICE.update({x['path']:x for x in tool})
    return inventory

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
            if str(p) in TOOL_ADVICE and row!=TOOL_ADVICE[str(p)]:raise RuntimeError('Pinned toolchain object drift')
            if expected is not None and row!=expected:raise RuntimeError('Inventory identity/hash mismatch')
            if advice_log is not None and eligible(p):
                if expected is None:raise RuntimeError('Eligible advice requires inventoried identity/hash')
                if before.st_mode & 0o111:
                    if str(p) in TOOL_ADVICE:raise RuntimeError('Pinned toolchain object unexpectedly executable; no advice')
                    event['excluded']='executable mode; no advice'
                else:
                    event['advice_scope']='toolchain_immutable_object' if str(p) in TOOL_ADVICE else 'dependency'
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
