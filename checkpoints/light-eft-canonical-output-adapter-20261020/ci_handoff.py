"""Admit committed bytes and the already successful decoder from this CI run only.

No fetch, compiler, lease acquisition, alternate carrier or historical path is
accepted here. The original four-stage receipt verifier is used unchanged.
"""
from pathlib import Path
import csv,importlib.util,json,os,re
from contracts import bind,regular,require,unchanged
from ci_handoff_contract import CONTRACT
from ci_policy import QUALIFICATION
from ci_staged_inputs import STAGED,SUFFIXES,reviewed_staged_inputs

def load(path):
    row,raw=regular(path)
    return row,json.loads(raw)

def indexed_evidence(root):
    """Bind the completed decoder's exact evidence set, including every output."""
    root=Path(root)
    require(root.is_dir() and not root.is_symlink(),'Missing/symlink same-run decoder root')
    index,rows=load(root/'evidence-sha256.json')
    require(isinstance(rows,list) and rows,'Absent decoder evidence index')
    protected={index['path']:index};seen=set()
    for r in rows:
        require(set(r)=={'path','bytes','sha256'},'Decoder evidence row schema differs')
        rel=Path(r['path'])
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) not in seen and str(rel)!='evidence-sha256.json','Unsafe/duplicate decoder evidence path')
        seen.add(str(rel));p=root/rel;protected[str(p)]=bind(p,r)
    actual=set()
    for p in root.rglob('*'):
        require(not p.is_symlink(),'Symlink decoder evidence member')
        if p.is_file():actual.add(str(p.relative_to(root)))
        else:require(p.is_dir(),'Nonregular decoder evidence member')
    require(actual==seen|{'evidence-sha256.json'},'Missing/unbound decoder evidence file')
    return protected

def decoder_policy(repo):
    path=Path(repo)/CONTRACT['decoder']['policy_path']
    spec=importlib.util.spec_from_file_location('_accepted_same_run_decoder_policy',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def prior_bindings(raw):
    """Decode the journal already authenticated by the decoder's receipts/index."""
    require(isinstance(raw,str) and raw and raw.endswith('\n'),'Incomplete decoder input journal')
    rows={}
    for line in raw.splitlines():
        row=json.loads(line)
        require(isinstance(row,dict) and set(row)=={'path','bytes','sha256','identity'},'Decoder input row schema differs')
        require(isinstance(row['path'],str) and type(row['bytes']) is int and row['bytes']>=0 and
            isinstance(row['sha256'],str) and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None and
            isinstance(row['identity'],list) and len(row['identity'])==5 and
            all(type(n) is int for n in row['identity']) and row['identity'][2]==row['bytes'],
            'Decoder input binding value schema differs')
        path=row['path'];p=Path(path)
        require(p.is_absolute() and str(p)==path and '..' not in p.parts and path not in rows,'Unsafe/duplicate decoder input path')
        rows[path]=row
    return rows

def retained_context(decoder,roots,fresh_semantic,fresh_inputs):
    """Compare existing observations only. Do not read, hash or rebaseline inputs.

    All old journal rows must match a current exact binding. Within each retained
    search root, semantic membership must also be equal in both directions; this
    catches new companions and runtime inputs as well as removals/changes.
    New carrier/control inputs outside those roots are permitted, independently
    authenticated by the current finite specification.
    """
    roots=list(map(Path,roots))
    require(list(map(str,roots))==decoder['retained_roots'],'Decoder retained search roots differ')
    previous=decoder['prior_bindings']
    for path,row in previous.items():
        require(fresh_inputs.get(path)==row,'Decoder retained input binding changed/missing: '+path)
    def retained(path):return any(Path(path).is_relative_to(root) for root in roots)
    old={path:row for path,row in previous.items() if retained(path)}
    fresh={path:row for path,row in fresh_semantic.items() if retained(path)}
    require(set(old)==set(fresh),'Decoder retained semantic membership added/missing: '+
        repr(dict(added=sorted(set(fresh)-set(old)),missing=sorted(set(old)-set(fresh)))))
    require(old==fresh,'Decoder retained semantic companion/runtime binding differs')
    return dict(previous_journal_rows=len(previous),matched_previous_journal_rows=len(previous),
        retained_semantic_rows=len(old),retained_roots=list(map(str,roots)),
        added_semantic_rows=0,missing_semantic_rows=0,changed_semantic_rows=0,
        strategy='Exact prior-journal equality against already computed fresh semantic inventory and exact input bindings; no additional hashing')

def verify_decoder(repo,tool,env,identity,spec,verify_receipts):
    root=Path(env['RUNNER_TEMP'])/('light-eft-staged-'+identity['GITHUB_RUN_ID']+'-'+identity['GITHUB_RUN_ATTEMPT'])
    protected=indexed_evidence(root)
    def document(rel):
        p=root/rel;require(str(p) in protected,'Unindexed required decoder evidence: '+rel)
        return load(p)[1]
    result=document('result.json');lease=document('lease.json');owner=document('fresh-CI-owner.json')
    claim=document('production-claim.json')
    require(result.get('accepted') is True and not result.get('failure'),'Decoder gate did not succeed')
    require(result.get('CI_identity')==identity and owner.get('identity')==identity and claim==identity,'Wrong decoder CI commit/run/attempt/event identity')
    require(result.get('source_commit')==result.get('harness_commit')==owner.get('source_commit')==identity['GITHUB_SHA'],'Wrong decoder source/harness commit')
    require(result.get('dependency_qualification')==QUALIFICATION,'Decoder provenance qualification differs')
    require(owner.get('boot_id')==lease.get('boot_id')==Path('/proc/sys/kernel/random/boot_id').read_text().strip(),'Decoder boot differs')
    current={n:os.readlink('/proc/self/ns/'+n) for n in ['pid','mnt','cgroup']}
    require(owner.get('namespaces')==lease.get('namespace')==current,'Decoder namespace differs')
    require(lease.get('state')=='released' and lease.get('kernel_echild') is True and not lease.get('release_errors'),'Decoder lifecycle/release incomplete')
    lock=root/'ci-single-compiler.lock';require(lease.get('path')==str(lock),'Decoder lease path differs')
    s=lock.lstat();d=root.lstat()
    require([s.st_dev,s.st_ino]==[lease.get('device'),lease.get('inode')] and [d.st_dev,d.st_ino]==lease.get('directory_identity'),'Decoder released lease identity differs')
    _,oldspec=load(Path(repo)/CONTRACT['decoder']['spec_path']);policy=decoder_policy(repo);policy.scope_contract(oldspec)
    require(oldspec['sources']['source']=={k:CONTRACT['decoder']['source'][k] for k in ['path','bytes','sha256']},'Decoder source fingerprint differs')
    packages=Path(repo)/'.lake/packages'
    dependency_roots=[packages/n/'.lake/build/lib/lean' for n in oldspec['pins'] if (packages/n/'.lake/build/lib/lean').is_dir()]
    work=root/'work';roots=[work/'objects',Path(repo)/'.lake/build/lib/lean',*dependency_roots,Path(tool)/'lib/lean']
    commands=policy.plans(repo,tool,work,oldspec,roots,identity['GITHUB_SHA'])
    for p in commands:p['source_bindings']=[bind(x) for x in p['sources']]
    dependencies={r['module']:dict(bind(Path(repo)/'.lake/build/lib/lean'/Path(*r['module'].split('.')).with_suffix('.olean')),module=r['module']) for r in oldspec['dependencies']}
    verify_receipts(root/'runtime',lease,commands,dependencies,identity['GITHUB_SHA'],expected_source=identity['GITHUB_SHA'])
    receipts=[document('runtime/'+p['stage']+'/receipt.json') for p in commands]
    expected_stages=[dict(stage=p['stage'],attempt_id=r['attempt_id']) for p,r in zip(commands,receipts,strict=True)]
    require(result.get('stages')==expected_stages,'Decoder result/receipt stage schedule differs')
    for r in receipts:require(r.get('CI_identity')==identity and r.get('dependency_qualification')==QUALIFICATION,'Decoder child CI identity/source context differs')
    module=CONTRACT['decoder']['module'];primary=work/'objects'/Path(*module.split('.')).with_suffix('.olean')
    outputs=receipts[0].get('outputs_after',{}).get('new_objects')
    require(isinstance(outputs,list) and outputs,'Missing decoder emitted-object bindings')
    bypath={r['path']:r for r in outputs};require(len(bypath)==len(outputs),'Duplicate decoder object binding')
    for r in receipts:
        require(r.get('outputs_after',{}).get('new_objects')==outputs,'Decoder emitted objects changed between stages')
    actual={str(p) for p in (work/'objects').rglob('*') if p.is_file()}
    require(actual==set(bypath),'Missing/unbound decoder object companion')
    stem=str(primary)[:-len('.olean')];parts=[]
    for p,r in sorted(bypath.items()):
        require(p.startswith(stem) and p[len(stem):] in SUFFIXES,'Wrong decoder object/prefix companion')
        require(bind(p)==r and protected.get(p)==r,'Decoder actual companion bytes/identity differ from receipts')
        parts.append(dict(suffix=p[len(stem):],bytes=r['bytes'],sha256=r['sha256']))
    semantic={r['suffix'] for r in parts}&{'.olean','.olean.server','.olean.private'}
    require(semantic in [{'.olean'},{'.olean','.olean.server','.olean.private'}],'Incomplete decoder module parts')
    require('.ir.sig' not in {r['suffix'] for r in parts} or '.ir' in {r['suffix'] for r in parts},'Decoder signature missing IR')
    require((root/'runtime/replay/raw.log').read_text().strip()=='replaying '+module,'Wrong decoder singleton replay diagnostic')
    _,resolution=load(work/'resolution.json')
    require(resolution.get('target')==module and resolution.get('count')==1 and resolution.get('resolved')==[{'module':module,'object':str(primary)}],'Decoder singleton resolution differs')
    require(list(dict.fromkeys(resolution.get('search_path',[])))==list(map(str,roots)),'Decoder effective search path differs')
    audit=result.get('result',{}).get('audit',{})
    with (work/'audit/ci-evidence/actual-owner-inventory.tsv').open() as f:owners=list(csv.DictReader(f,delimiter='\t'))
    require(audit.get('new_owner_roots')==len(owners)==43 and set(audit.get('project_imports',[]))==set(dependencies)|{module},'Decoder accepted audit scope differs')
    require(audit.get('private_identity_helper')==policy.private_helper(owners) and audit.get('strict_findings')==0,'Decoder private helper/strict audit differs')
    item=dict(module=module,source_sha256=CONTRACT['decoder']['source']['sha256'],layout='module' if len(semantic)==3 else 'legacy',parts=parts)
    previous=prior_bindings((root/'runtime/inputs.jsonl').read_text())
    return dict(root=root,protected=protected,item=item,paths={r['suffix']:stem+r['suffix'] for r in parts},lease=lease,stages=expected_stages,
        prior_bindings=previous,retained_roots=list(map(str,roots[1:])))

def static_records(repo,spec):
    source={r['module']:r for r in spec['dependencies']};items=[];paths={};protected={}
    for row in CONTRACT['static_objects']:
        module=row['module'];require(source.get(module)==row['source'],'Recovered object source binding differs')
        for record in [row['source'],row['object']]:
            p=Path(repo)/record['path'];protected[str(p)]=bind(p,record)
        stem=Path(repo)/row['object']['path'][:-len('.olean')]
        actual={str(p) for p in stem.parent.iterdir() if p.name==stem.name or p.name.startswith(stem.name+'.')}
        require(actual=={str(stem)+'.olean'},'Missing/changed static companion or unbound static object extra')
        part=dict(suffix='.olean',bytes=row['object']['bytes'],sha256=row['object']['sha256'])
        items.append(dict(module=module,source_sha256=row['source']['sha256'],layout='legacy',parts=[part]))
        paths[module]={'.olean':str(stem)+'.olean'}
    return items,paths,protected

def admit_carrier(path,reference,spec,expected_objects):
    require(bind(path)==reference,'Admitted carrier manifest changed')
    _,doc=load(path)
    require(doc.get('objects')==expected_objects,'Carrier differs from independently verified object bindings')
    scoped=dict(spec,accepted_staged_manifest_sha256=reference['sha256'])
    return reviewed_staged_inputs(scoped,{'LIGHTEFT_COROLLARY_ACCEPTED_INPUTS':str(path)})

def prepare_inputs(root,repo,spec,decoder):
    items,paths,protected=static_records(repo,spec)
    items.append(decoder['item']);paths[decoder['item']['module']]=decoder['paths']
    require({r['module'] for r in items}==set(STAGED),'Wrong finite object carrier set')
    carrier=Path(root)/'admitted-inputs';require(not carrier.exists(),'Fresh admitted carrier required; no retry')
    objects=carrier/'objects';objects.mkdir(parents=True)
    for item in items:
        stem=objects/Path(*item['module'].split('.'));stem.parent.mkdir(parents=True,exist_ok=True)
        for part in item['parts']:
            source=Path(paths[item['module']][part['suffix']]);row,raw=regular(source)
            require(row['sha256']==part['sha256'] and row['bytes']==part['bytes'],'Changed verified carrier source')
            p=Path(str(stem)+part['suffix'])
            with p.open('xb') as f:f.write(raw)
    doc=dict(scope='CANONICAL_ACTUAL_OUTPUT_IMPORTS_ONLY',source_base=CONTRACT['accepted_source_base'],root='objects',
        provenance_qualification=QUALIFICATION,objects=items)
    path=carrier/'manifest.json'
    with path.open('x') as f:json.dump(doc,f,indent=2);f.write('\n')
    reference=bind(path);staged,bindings,layouts=admit_carrier(path,reference,spec,items)
    protected.update(decoder['protected']);protected.update(bindings)
    unchanged(protected)
    return dict(root=staged,protected=protected,layouts=layouts,manifest=path,reference=reference,objects=items)
