"""Fresh CI observation only; historical/local input identities are never reused."""
from pathlib import Path
import stat

ARCHIVES={'libInit.a','libLake.a','libLean.a','libLeanChecker.a','libLeanIR.a','libLeanc.a','libStd.a','libleancpp.a','libleanmanifest.a','libleanrt.a'}
RUNTIME_SHARED={'libInit_shared.so','libLake_shared.so','libleanshared.so','libleanshared_1.so','libleanshared_2.so'}
METADATA=('.ilean.hash','.olean.hash','.olean.server.hash','.olean.private.hash','.ir.sig.hash','.ir.hash','.trace')
SEMANTIC=('.olean.private','.olean.server','.olean','.ilean','.ir.sig','.ir')

def directory_identity(st):
    return [st.st_dev,st.st_ino,stat.S_IMODE(st.st_mode),st.st_uid,st.st_gid]

def file_identity(st):
    return [st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns,
            stat.S_IMODE(st.st_mode),st.st_uid,st.st_gid,st.st_nlink]

class CIIdentityGuard:
    """Stat-only seal of fully verified inputs and exact tree membership.

    File identity includes ctime, mode, ownership and link count. Parents must
    remain the same real directories. Parent timestamps are intentionally not
    fixed: the supervisor legitimately replaces its receipt beside snapshots.
    Read-only input-tree directory identities come from the full inventory.
    """
    def __init__(self,bindings,members,directories):
        self.bindings=dict(bindings)
        self.members={str(p):set(names) for p,names in members.items()}
        self.directories=dict(directories)
        self.original=self.snapshot()

    def snapshot(self):
        files={};directories={};parents={};seen=set()
        for root,expected in self.members.items():
            root=Path(root);st=root.lstat()
            if not stat.S_ISDIR(st.st_mode):raise ValueError('Missing/symlink CI tree root')
            directories[str(root)]=file_identity(st)
            found=set()
            for p in root.rglob('*'):
                st=p.lstat();path=str(p);found.add(path)
                if stat.S_ISDIR(st.st_mode):directories[path]=file_identity(st)
                elif not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:
                    raise ValueError('Nonregular/linked CI tree member: '+path)
            if found!=expected:raise ValueError('CI exact membership changed: '+str(root))
        for path,row in self.bindings.items():
            p=Path(path);st=p.lstat()
            if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:
                raise ValueError('Nonregular/linked CI bound input: '+path)
            identity=file_identity(st)
            if identity[:5]!=row['identity']:raise ValueError('CI bound input identity changed: '+path)
            files[path]=identity
        for path,expected in self.directories.items():
            st=Path(path).lstat()
            if not stat.S_ISDIR(st.st_mode) or directory_identity(st)!=expected:
                raise ValueError('CI input directory identity changed: '+path)
        for path in [*self.bindings,*self.members,*directories]:
            for parent in Path(path).absolute().parents:
                name=str(parent)
                if name in seen:break
                st=parent.lstat()
                if not stat.S_ISDIR(st.st_mode):raise ValueError('Symlink/non-directory CI parent: '+name)
                parents[name]=directory_identity(st);seen.add(name)
        return dict(files=files,directories=directories,parents=parents,members=self.members)

    def verify(self):
        if self.snapshot()!=self.original:raise ValueError('CI preexec identity/membership changed')

class CIInventory:
    def __init__(self,roots,tool,bind):
        self.roots=list(map(Path,roots));self.tool=Path(tool);self.bind=bind;self.original=None
        if len(set(map(str,self.roots)))!=len(self.roots):raise ValueError('Duplicate CI search root')

    def scan(self):
        semantic={};excluded={};members={};all_paths={};directories={}
        for root in self.roots:
            if root.is_symlink() or not root.is_dir():raise ValueError('Invalid CI search root')
            for parent in root.parents:
                if parent.is_symlink():raise ValueError('CI search-root parent symlink')
            directories[str(root)]=directory_identity(root.lstat())
            found=set()
            for p in root.rglob('*'):
                st=p.lstat()
                if stat.S_ISDIR(st.st_mode):
                    directories[str(p)]=directory_identity(st);continue
                if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('Nonregular/linked CI input')
                path=str(p)
                if path in all_paths:raise ValueError('Duplicate CI physical input')
                all_paths[path]=p;found.add(path)
                metadata=next((s for s in METADATA if path.endswith(s)),None)
                if p.parent==self.tool/'lib/lean' and p.name in ARCHIVES:
                    excluded[path]=dict(path=path,bytes=st.st_size,identity=[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns],metadata_only=True)
                elif p.parent==self.tool/'lib/lean' and p.name in RUNTIME_SHARED:
                    # ci_gate includes this map in inputs.jsonl and preservation checks.
                    # These are hashed runtime inputs, never metadata exclusions.
                    semantic[path]=self.bind(p)
                elif metadata:
                    if not Path(path[:-len(metadata)]+'.olean').is_file():raise ValueError('Orphan CI metadata family')
                    excluded[path]=dict(path=path,bytes=st.st_size,identity=[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns],metadata_only=True)
                else:
                    suffix=next((s for s in SEMANTIC if path.endswith(s)),None)
                    if suffix is None:raise ValueError('Unknown CI search input: '+path)
                    stem=path[:-len(suffix)]
                    if suffix!='.olean' and not Path(stem+'.olean').is_file():raise ValueError('Orphan CI semantic family')
                    if suffix=='.ir.sig' and not Path(stem+'.ir').is_file():raise ValueError('CI signature without IR family')
                    semantic[path]=self.bind(p)
            members[str(root)]=found
        if self.tool/'lib/lean' in self.roots:
            required={str(self.tool/'lib/lean'/name) for name in RUNTIME_SHARED}
            if not required.issubset(semantic):raise ValueError('Missing CI toolchain shared runtime input')
        observed=dict(semantic=semantic,excluded=excluded,members=members,directories=directories)
        if self.original is None:self.original=observed
        elif observed!=self.original:raise ValueError('Fresh CI input content/identity/membership changed')
        return observed
