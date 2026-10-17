"""Acquire a reviewed dependency-only object artifact without invoking Lean/Lake.
No fallback to Cache.Main: its initializer spawns a hidden Lean process.
"""
from pathlib import Path, PurePosixPath
import hashlib,json,re,tarfile,urllib.request

MANIFEST='dependency-cache-manifest.json'
SUFFIXES=('.olean.private','.olean.server','.olean','.ilean','.ir')

def digest(path):
    with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def reviewed_spec(path,pins,manifest_hash):
    spec=json.loads(Path(path).read_text())
    if spec.get('status')!='REVIEWED_ARTIFACT':
        raise RuntimeError('BLOCKED: no reviewed dependency-only cache artifact/provenance is pinned')
    for field in ['sha256','manifest_sha256']:
        if not re.fullmatch('[0-9a-f]{64}',spec.get(field,'')):raise ValueError('Missing artifact '+field)
    if spec.get('pins')!={p['name']:p['rev'] for p in pins} or spec.get('lake_manifest_sha256')!=manifest_hash:
        raise ValueError('Dependency artifact pins differ')
    if spec.get('toolchain')!='leanprover/lean4:v4.34.0':raise ValueError('Wrong artifact toolchain')
    if not isinstance(spec.get('bytes'),int) or spec['bytes']<=0:raise ValueError('Artifact size required')
    if not spec.get('url','').startswith('https://') or not spec.get('provenance_review','').startswith('https://github.com/'):
        raise ValueError('Immutable artifact URL and independently reviewed provenance link required')
    return spec

def dependency_file(path,pins):
    parts=PurePosixPath(path).parts
    if str(PurePosixPath(path))!=path or not path or path.startswith('/') or any(x in ('.','..') for x in path.split('/')) or '\\' in path:
        raise ValueError('Unsafe artifact path')
    if len(parts)<8 or parts[:2]!=('.lake','packages') or parts[2] not in pins or parts[3:7]!=('.lake','build','lib','lean'):
        raise ValueError('Not a dependency object path: '+path)
    relative='/'.join(parts[7:]);suffix=next((s for s in SUFFIXES if relative.endswith(s)),None)
    if suffix is None:raise ValueError('Unapproved dependency object type: '+path)
    module=relative[:-len(suffix)]
    if module.split('/')[0] in ('LightEFTSpanners','LightSpanners'):
        raise ValueError('Inherited project object forbidden')
    return parts[2],module+'.lean'

def install(archive,spec,root,evidence):
    """Validate entire inventory before writing; manually copy regular files only."""
    root=Path(root);evidence=Path(evidence)
    if Path(archive).stat().st_size!=spec['bytes'] or digest(archive)!=spec['sha256']:
        raise ValueError('Dependency artifact hash/size mismatch')
    with tarfile.open(archive,'r:*') as tar:
        members=tar.getmembers();names=[m.name for m in members]
        if len(names)!=len(set(names)) or any(not m.isfile() for m in members):
            raise ValueError('Only unique regular-file members are permitted')
        if MANIFEST not in names:raise ValueError('Missing dependency artifact manifest')
        raw=tar.extractfile(MANIFEST).read()
        if hashlib.sha256(raw).hexdigest()!=spec['manifest_sha256']:raise ValueError('Manifest hash mismatch')
        (evidence/MANIFEST).write_bytes(raw)
        manifest=json.loads(raw)
        for key in ['pins','toolchain','lake_manifest_sha256']:
            if manifest.get(key)!=spec[key]:raise ValueError('Manifest mismatch: '+key)
        # Provenance is human-reviewed at the hash-pinned spec, not inferred from a URL.
        provenance=manifest.get('official_archives',[])
        if not provenance or any(not p.get('url','').startswith('https://cache.mathlib.org/') or not re.fullmatch('[0-9a-f]{64}',p.get('sha256','')) for p in provenance):
            raise ValueError('Missing official cache archive provenance')
        origins={p['sha256'] for p in provenance}
        rows=manifest['files'];paths=[r['path'] for r in rows]
        if len(paths)!=len(set(paths)) or set(names)!={MANIFEST,*paths}:raise ValueError('Artifact inventory mismatch')
        for row in rows:
            package,source=dependency_file(row['path'],spec['pins'])
            if row.get('archive_sha256') not in origins:raise ValueError('Unbound cache provenance')
            source_path=root/'.lake/packages'/package/source
            if digest(source_path)!=row['source_sha256']:raise ValueError('Dependency source hash mismatch')
            member=tar.getmember(row['path'])
            if member.size!=row['bytes']:raise ValueError('Object size mismatch')
            with tar.extractfile(member) as stream:
                if hashlib.file_digest(stream,'sha256').hexdigest()!=row['sha256']:raise ValueError('Object hash mismatch')
            target=root/row['path']
            if target.exists():raise ValueError('Existing dependency object would be overwritten')
            if any(parent.is_symlink() for parent in [target,*target.parents]):raise ValueError('Symlink output path')
        for row in rows:
            target=root/row['path'];target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as output,tar.extractfile(row['path']) as source:
                while chunk:=source.read(1024*1024):output.write(chunk)
            if digest(target)!=row['sha256']:raise ValueError('Installed object mismatch')
    result=dict(artifact_sha256=spec['sha256'],manifest_sha256=spec['manifest_sha256'],objects=len(rows),
                provenance_review=spec['provenance_review'],lean_invocations=0,project_objects=0)
    (evidence/'dependency-artifact-installed.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def acquire(spec,root,evidence):
    evidence=Path(evidence);partial=evidence/'dependency-cache.tar.part';archive=evidence/'dependency-cache.tar'
    # Failed downloads remain intact for diagnosis. No subprocess or compiler.
    with urllib.request.urlopen(spec['url'],timeout=60) as response,partial.open('xb') as output:
        if not response.geturl().startswith('https://'):raise ValueError('Insecure artifact redirect')
        size=0
        while chunk:=response.read(1024*1024):
            size+=len(chunk)
            if size>spec['bytes']:raise ValueError('Artifact exceeds reviewed size')
            output.write(chunk)
    if size!=spec['bytes'] or digest(partial)!=spec['sha256']:raise ValueError('Downloaded artifact mismatch')
    partial.rename(archive)
    return install(archive,spec,root,evidence)
