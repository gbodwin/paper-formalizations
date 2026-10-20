"""Read a separately reviewed finite accepted-object carrier; never build or fetch."""
from pathlib import Path
import hashlib,json,os,re
from contracts import bind,regular,require

STAGED=(
 'LightEFTActualSuppliedForestProbabilityStage.PolynomialActualFailureProbability',
 'LightEFTJointFlagSamplingStage.JointAssignmentLaw',
 'LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability',
 'LightEFTSuppliedForestStage.SuppliedForestGoodEvent',
)
SUFFIXES={'.olean','.olean.server','.olean.private','.ilean','.ir','.ir.sig'}
OLEAN_PARTS={'.olean','.olean.server','.olean.private'}
REQUIRED={'.olean'}

def reviewed_staged_inputs(spec,env):
    expected=spec.get('accepted_staged_manifest_sha256')
    require(re.fullmatch('[0-9a-f]{64}',expected or '') is not None,'No reviewed accepted-object manifest')
    name=env.get('LIGHTEFT_COROLLARY_ACCEPTED_INPUTS','');path=Path(name)
    require(name and path.is_absolute() and '..' not in path.parts,'Explicit current accepted-object manifest path required')
    row,raw=regular(path);require(hashlib.sha256(raw).hexdigest()==expected,'Accepted-object manifest changed')
    doc=json.loads(raw)
    require(set(doc)=={'scope','source_base','root','provenance_qualification','objects'},'Accepted-object manifest schema differs')
    require(doc.get('scope')=='CANONICAL_ACTUAL_OUTPUT_IMPORTS_ONLY','Wrong accepted-object scope')
    require(doc.get('source_base')==spec['accepted_source_base'],'Wrong accepted-object source base')
    require(doc.get('provenance_qualification')==spec['dependency_qualification'],'Dependency provenance qualification changed')
    require(doc['root']=='objects','Portable sibling objects root required; historical absolute roots refused')
    root=path.parent/'objects';require(root.is_dir() and not root.is_symlink(),'Invalid current accepted-object root')
    for parent in root.parents:require(not parent.is_symlink(),'Symlink accepted-object ancestor')
    rows=doc['objects'];require(len(rows)==4 and {r['module'] for r in rows}==set(STAGED),'Exact four accepted staged dependencies required')
    source={r['module']:r for r in spec['dependencies']};protected={str(path):row};expected_paths=set();expected_dirs=set();layouts={}
    for item in rows:
        require(set(item)=={'module','source_sha256','layout','parts'},'Staged module record schema differs')
        module=item['module'];require(item['source_sha256']==source[module]['sha256'],'Staged object/source fingerprint differs')
        parts=item['parts'];suffixes=[part['suffix'] for part in parts]
        require(item['layout'] in ('legacy','module'),'Explicit reviewed object layout required')
        required=REQUIRED if item['layout']=='legacy' else OLEAN_PARTS
        layouts[module]=len(required)
        require(len(suffixes)==len(set(suffixes)) and set(suffixes)<=SUFFIXES and set(suffixes)&OLEAN_PARTS==required,'Missing/duplicate/unknown semantic staged parts or wrong layout')
        require('.ir.sig' not in suffixes or '.ir' in suffixes,'Signature without IR')
        stem=root/Path(*module.split('.'))
        for part in parts:
            require(set(part)=={'suffix','bytes','sha256'} and type(part['bytes']) is int and part['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',part['sha256']) is not None,'Semantic part binding schema differs')
            q=Path(str(stem)+part['suffix']);expected_paths.add(str(q));protected[str(q)]=bind(q,part)
            for parent in q.parents:
                if parent==root:break
                expected_dirs.add(str(parent))
    found=set();found_dirs=set()
    for q in root.rglob('*'):
        require(not q.is_symlink(),'Symlink staged carrier member')
        if q.is_file():found.add(str(q))
        else:
            require(q.is_dir(),'Nonregular staged carrier member');found_dirs.add(str(q))
    require(found==expected_paths,'Unbound/missing staged carrier file')
    require(found_dirs==expected_dirs,'Unexpected/missing staged carrier directory')
    return root,protected,layouts
