"""Conservative Linux cgroup-v2 admission; no hidden-ancestor assumption.
Only the kernel's initial cgroup namespace and a visible full hierarchy are
supported. Namespaced/truncated views fail closed, even if visible limits look ample.
"""
from pathlib import Path, PurePosixPath
import os, re

# Linux include/uapi/linux/nsfs.h: CGROUP_NS_INIT_INO. Unknown platforms refuse.
INITIAL_CGROUP_NS_INO = 0xEFFFFFFB

def unescape(value):
    return re.sub(r'\\(040|011|012|134)', lambda m: chr(int(m[1],8)), value)

def absolute(value):
    if not value.startswith('/') or any(p in ('.','..') for p in value.split('/')) or ' (deleted)' in value:
        raise ValueError('Ambiguous/deleted/nonabsolute cgroup path: '+value)
    return PurePosixPath(value)

def discover(cgroup_text, mountinfo_text, namespace_inode, read_file):
    if namespace_inode != INITIAL_CGROUP_NS_INO:
        raise ValueError('Non-initial cgroup namespace: hidden ancestor limits cannot be established')
    memberships=[line[3:] for line in cgroup_text.splitlines() if line.startswith('0::')]
    if len(memberships)!=1:raise ValueError('Exactly one unified cgroup membership required')
    member=absolute(memberships[0]); mounts=[]
    for line in mountinfo_text.splitlines():
        fields=line.split(); split=fields.index('-')
        if fields[split+1]!='cgroup2':continue
        root=absolute(unescape(fields[3])); point=absolute(unescape(fields[4]))
        mounts.append(dict(root=str(root),mountpoint=str(point),device=fields[2]))
    full=[m for m in mounts if m['root']=='/']
    if not full or len({m['device'] for m in full})!=1:
        raise ValueError('No unambiguous full cgroup-v2 hierarchy; ancestors may be hidden')
    chosen=min(full,key=lambda m:(len(m['mountpoint']),m['mountpoint']))
    base=PurePosixPath(chosen['mountpoint'])
    # The verified initial hierarchy root is exempt by kernel semantics, not by
    # interpreting a missing memory.max as infinity. Require its controller metadata.
    controllers=read_file(str(base/'cgroup.controllers')).split()
    if 'memory' not in controllers:raise ValueError('Root memory controller unavailable')
    if read_file(str(base/'cgroup.type')).strip()!='domain':raise ValueError('Unexpected root domain')
    ancestors=[]; cur=member
    while cur!=PurePosixPath('/'):
        directory=base/cur.relative_to('/')
        current_text=read_file(str(directory/'memory.current')).strip()
        limit_text=read_file(str(directory/'memory.max')).strip()
        if not current_text.isdecimal() or (limit_text!='max' and not limit_text.isdecimal()):
            raise ValueError('Malformed cgroup memory accounting at '+str(directory))
        current=int(current_text);limit=None if limit_text=='max' else int(limit_text)
        ancestors.append(dict(cgroup=str(cur),directory=str(directory),current=current,max=limit_text,
                              headroom=None if limit is None else limit-current))
        cur=cur.parent
    finite=[row['headroom'] for row in ancestors if row['headroom'] is not None]
    return dict(membership=str(member),mounts=mounts,selected_mount=chosen,ancestors=ancestors,
                initial_namespace_verified=True,global_root='not a resource-controlled domain (kernel semantics)',
                cgroup_headroom=min(finite) if finite else None,
                explicit_unlimited=not finite)

def memory_snapshot():
    snapshot={}
    try:
        snapshot['meminfo']=Path('/proc/meminfo').read_text()
        fields=[line.split() for line in snapshot['meminfo'].splitlines() if line.startswith('MemAvailable:')]
        if len(fields)!=1 or len(fields[0])!=3 or fields[0][2]!='kB':raise ValueError('Bad MemAvailable')
        snapshot['system_available']=int(fields[0][1])*1024
        snapshot['cgroup_membership_raw']=Path('/proc/self/cgroup').read_text()
        snapshot['mountinfo_raw']=Path('/proc/self/mountinfo').read_text()
        snapshot['namespace_inode']=os.stat('/proc/self/ns/cgroup').st_ino
        snapshot.update(discover(snapshot['cgroup_membership_raw'],snapshot['mountinfo_raw'],
                                 snapshot['namespace_inode'],lambda p:Path(p).read_text()))
        if Path('/proc/self/cgroup').read_text()!=snapshot['cgroup_membership_raw'] or os.stat('/proc/self/ns/cgroup').st_ino!=snapshot['namespace_inode']:
            raise ValueError('Cgroup membership changed during observation')
        if Path('/proc/self/mountinfo').read_text()!=snapshot['mountinfo_raw']:
            raise ValueError('Mount layout changed during observation')
    except (OSError,ValueError,IndexError) as exc:
        snapshot['discovery_error']=repr(exc)
    return snapshot
