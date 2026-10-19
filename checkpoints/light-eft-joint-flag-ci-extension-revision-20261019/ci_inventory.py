"""Fresh CI observation only; historical/local input identities are never reused."""
from pathlib import Path
import stat

ARCHIVES={'libInit.a','libLake.a','libLean.a','libLeanChecker.a','libLeanIR.a','libLeanc.a','libStd.a','libleancpp.a','libleanmanifest.a','libleanrt.a'}
RUNTIME_SHARED={'libInit_shared.so','libLake_shared.so','libleanshared.so','libleanshared_1.so','libleanshared_2.so'}
METADATA=('.ilean.hash','.olean.hash','.olean.server.hash','.olean.private.hash','.ir.sig.hash','.ir.hash','.trace')
SEMANTIC=('.olean.private','.olean.server','.olean','.ilean','.ir.sig','.ir')

class CIInventory:
    def __init__(self,roots,tool,bind):
        self.roots=list(map(Path,roots));self.tool=Path(tool);self.bind=bind;self.original=None
        if len(set(map(str,self.roots)))!=len(self.roots):raise ValueError('Duplicate CI search root')

    def scan(self):
        semantic={};excluded={};members={};all_paths={}
        for root in self.roots:
            if root.is_symlink() or not root.is_dir():raise ValueError('Invalid CI search root')
            for parent in root.parents:
                if parent.is_symlink():raise ValueError('CI search-root parent symlink')
            found=set()
            for p in root.rglob('*'):
                st=p.lstat()
                if stat.S_ISDIR(st.st_mode):continue
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
        observed=dict(semantic=semantic,excluded=excluded,members=members)
        if self.original is None:self.original=observed
        elif observed!=self.original:raise ValueError('Fresh CI input content/identity/membership changed')
        return observed
