"""Fail-closed reconciliation of fresh audit outputs, never a Lean invocation."""
from pathlib import Path
import collections, hashlib, json, os, re, stat
from audit_outputs import OUTPUTS, DECISION_LIMIT, bind_outputs

ALLOWED = {'propext','Classical.choice','Quot.sound'}
KINDS = {'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}


def project(owner):
    return any(owner==p or owner.startswith(p+'.') for p in ['LightSpanners','LightEFTSpanners'])


def table(path, header):
    data=Path(path).read_bytes()
    if not data.endswith(b'\n'): raise RuntimeError('Incomplete TSV final row: '+str(path))
    lines=data.decode('utf-8').splitlines()
    if not lines or lines[0].split('\t')!=header: raise RuntimeError('Unexpected TSV header: '+str(path))
    rows=[]
    for line in lines[1:]:
        values=line.split('\t')
        if len(values)!=len(header): raise RuntimeError('Malformed TSV row: '+str(path))
        rows.append(dict(zip(header,values)))
    return rows


def validate_tables(ci, required_modules, raw_text):
    ci=Path(ci); required=set(required_modules)
    loaded_data=(ci/'import-closure-loaded.txt').read_bytes()
    if not loaded_data.endswith(b'\n'): raise RuntimeError('Truncated loaded-module export')
    loaded=loaded_data.decode('utf-8').splitlines()
    if not loaded or any(not x for x in loaded) or len(loaded)!=len(set(loaded)):
        raise RuntimeError('Empty/duplicate loaded-module export')
    if not required.issubset(loaded) or 'LightEFTSpanners' not in loaded:
        raise RuntimeError('Missing required ordinary module or aggregate import')
    if {m for m in loaded if project(m)}-required-{'LightEFTSpanners'}:
        raise RuntimeError('Unexpected project module outside frozen486source graph')
    if (ci/'strict-violations.txt').read_bytes()!=b'\n': raise RuntimeError('Fresh strict findings are nonempty/malformed')
    inventory=table(ci/'actual-owner-inventory.tsv',['owner','name','kind','unsafe','partial'])
    closure=table(ci/'recursive-dependencies.tsv',['name','owner','kind','typeDependencies','bodyDependencies','unsafe','partial'])
    inv={row['name']:row for row in inventory}; dep={row['name']:row for row in closure}
    if not inventory or len(inv)!=len(inventory) or len(dep)!=len(closure): raise RuntimeError('Empty/duplicate actual-owner or closure rows')
    for row in inventory+closure:
        if not row['name'] or row['kind'] not in KINDS: raise RuntimeError('Unknown/empty declaration name or kind')
        if row['unsafe']!='false' or row['partial']!='false': raise RuntimeError('Unsafe/partial declaration: '+row['name'])
    for row in inventory:
        if not project(row['owner']) or row['owner'] not in loaded: raise RuntimeError('Inventory owner is not a loaded project module')
        if row['kind']=='axiom': raise RuntimeError('Project axiom: '+row['name'])
        other=dep.get(row['name'])
        if other is None or any(other[key]!=row[key] for key in ['owner','kind','unsafe','partial']):
            raise RuntimeError('Actual-owner root absent/inconsistent in recursive closure')
    if {n for n,row in dep.items() if project(row['owner'])}!=set(inv):
        raise RuntimeError('Private/generated/project-owned closure declaration omitted from root inventory')
    axioms={row['name'] for row in closure if row['kind']=='axiom'}
    if not axioms.issubset(ALLOWED): raise RuntimeError('Disallowed recursive axiom: '+str(sorted(axioms-ALLOWED)))
    links={}
    for name,row in dep.items():
        names=[]
        for column in ['typeDependencies','bodyDependencies']:
            if row[column]: names+=row[column].split(',')
        # The pinned export uses comma-separated names. Ambiguous names or
        # unresolved references reject rather than silently losing coverage.
        if any(n not in dep for n in names): raise RuntimeError('Unresolved/ambiguous type/body dependency: '+name)
        if row['kind'] in ('inductive','constructor','recursor') and not row['bodyDependencies']:
            raise RuntimeError('Missing inductive/constructor/recursor-rule coverage: '+name)
        links[name]=names
    visited=set();todo=list(inv)
    while todo:
        name=todo.pop()
        if name in visited:continue
        visited.add(name);todo.extend(links[name])
    if visited!=set(dep): raise RuntimeError('Exported closure is not exactly the recursive type/body closure of all roots')
    pattern=r'DIAGNOSTIC ONLY: (\d+) actual-owner project declarations, (\d+) covered declarations; (\d+) recursively visited constants, (\d+) opaque bodies; axioms #?\[([^\]]*)\]'
    summaries=re.findall(pattern,raw_text,re.S)
    if len(summaries)!=1: raise RuntimeError('Missing/duplicate fresh audit diagnostic summary')
    roots,covered,constants,opaque,ax=summaries[0]
    printed={name.strip() for name in ax.split(',') if name.strip()}
    counts=(len(inv),sum(row['owner'] in required for row in inventory),len(dep),sum(row['kind']=='opaque' for row in closure))
    if tuple(map(int,[roots,covered,constants,opaque]))!=counts or printed!=axioms:
        raise RuntimeError('Fresh printed counts/axioms disagree with complete exports')
    if re.search(r'^(?:.*:\d+:\d+: )?(?:warning|error):',raw_text,re.M): raise RuntimeError('Unexpected Lean warning/error diagnostic')
    return {'actual_owner_roots':counts[0],'ordinary_module_owned_roots':counts[1],
        'visited_constants':counts[2],'opaque_bodies':counts[3],'axioms':sorted(axioms),
        'required_ordinary_modules_loaded':len(required),'loaded_modules':len(loaded),
        'private_generated_roots_included':True,'recursive_types_bodies_opaque_and_recursor_rules':True,
        'unsafe_partial_or_project_axioms':0,'strict_findings':0}


def chunk_file(source,directory,target=200000):
    """Copy complete byte rows in original order; never duplicate the header."""
    source=Path(source);directory=Path(directory);directory.mkdir(parents=True,exist_ok=False)
    parts=[];buffer=bytearray();number=0;whole=hashlib.sha256();total=0
    def flush():
        nonlocal buffer,number
        if not buffer:return
        p=directory/('part-%04d.txt'%number);p.write_bytes(buffer)
        parts.append({'path':p.name,'bytes':len(buffer),'sha256':hashlib.sha256(buffer).hexdigest(),
            'exceeds_target_single_row':len(buffer)>target})
        number+=1;buffer=bytearray()
    with source.open('rb') as f:
        for row in f:
            whole.update(row);total+=len(row)
            if buffer and len(buffer)+len(row)>target:flush()
            buffer.extend(row)
    flush()
    h=hashlib.sha256();size=0
    for item in parts:
        b=(directory/item['path']).read_bytes();h.update(b);size+=len(b)
    if h.hexdigest()!=whole.hexdigest() or size!=total: raise RuntimeError('Chunk reconstruction mismatch')
    result={'source':str(source),'bytes':total,'sha256':whole.hexdigest(),'row_aligned':True,
        'reconstruction':'Concatenate listed part bytes in order, without headers or separators.',
        'target_bytes':target,'parts':parts}
    (directory/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def reconcile_run(evidence, plan):
    E=Path(evidence);state=json.loads((E/'run-state.json').read_text())
    r=json.loads((E/'attempt/receipt.json').read_text());lease=json.loads((E/'batch-lock.json').read_text())
    A=Path(__file__).resolve().parent;R=A.parents[1]
    if state['attempts']!=1 or E!=A/'executions'/state['run_id']:
        raise RuntimeError('Not the one fresh execution directory')
    if r['source_commit']!=plan['source_commit'] or r['approved_adapter_commit']!=state['approved_adapter_commit']:
        raise RuntimeError('Source/reviewed adapter binding differs')
    if state.get('controller_failure') or not state.get('final_preservation',{}).get('matching'):
        raise RuntimeError('Controller failure or mandatory final preservation failed')
    if not state.get('Lean_exec_authorized'):raise RuntimeError('Fresh Lean exec was not authorized at preexec gate')
    if not (r['state']=='finished' and r['exit']==0 and not r.get('failure') and r['direct_reaped']
            and r['waitid_wait4_status_match'] and r['kernel_no_children_verified'] and r['all_descendants_gone']):
        raise RuntimeError('Fresh zero-exit owned audit/cleanup receipt required')
    if r['stage']!='audit' or r['stage_kind']!='audit_only' or r['argv']!=plan['argv'] or r['environment']!=plan['environment']:
        raise RuntimeError('Receipt does not describe the one exact audit invocation')
    if r['submitted_source_sha256']!=plan['audit_source']['sha256'] or hashlib.sha256((E/r['source_snapshot']).read_bytes()).hexdigest()!=r['submitted_source_sha256']:
        raise RuntimeError('Audit submitted-source hash mismatch')
    if r['attempt_id']!=state['attempt_id'] or r['audit_output_budget']!=state['fresh_output_spec']:
        raise RuntimeError('Fresh execution/output nonce binding differs')
    if (r['audit_output_budget']['work']!=str(R/'.lake'/('light-eft-full-audit-'+state['run_id']))
            or r['audit_output_budget']['raw']!=str(E/'attempt/raw.log') or not r['source_outputs_absent_before_exec']):
        raise RuntimeError('Fresh working directory/source-output absence not verified')
    if not lease['kernel_echild_at_release'] or lease['state']!='released' or [lease['device'],lease['inode']]!=[33,3849]:
        raise RuntimeError('Continuous lock/cleanup barrier not verified')
    if not lease['acquired_ns']<=r['started_ns']<=r['ended_ns']<=lease['release_verified_ns']:
        raise RuntimeError('Audit invocation outside continuous lease')
    initial=r['canonical_input_inventory'];final=state['final_preservation']
    if not (final['all_paths_attempted'] and final['paths_checked']==initial['rows'] and
            final['before_sha256']==final['after_stream_sha256']==initial['sha256']):
        raise RuntimeError('Initial/final complete inventory pair differs')
    protected=json.loads((A/'protected-bindings.json').read_text())['bindings']
    remaining={row['path']:row for row in protected};seen=set();hash_stream=hashlib.sha256();source_bound=False
    if len(remaining)!=900:raise RuntimeError('All486objects and414resolutions required')
    with (E/'inputs.jsonl').open('rb') as stream:
        for line in stream:
            hash_stream.update(line);row=json.loads(line)
            if row['path'] in seen:raise RuntimeError('Duplicate frozen inventory path')
            seen.add(row['path'])
            expected=remaining.pop(row['path'],None)
            if expected is not None and any(row[key]!=expected[key] for key in ['sha256','bytes','identity']):
                raise RuntimeError('Protected object/resolution not identically frozen')
            if row['path']==str(R/plan['audit_source']['path']):source_bound=row['sha256']==plan['audit_source']['sha256']
    if remaining or not source_bound or len(seen)!=initial['rows'] or hash_stream.hexdigest()!=initial['sha256']:
        raise RuntimeError('Complete fresh source/object/resolution inventory coverage failed')
    if not (r['terminal_confirmation']['terminal'] and r['terminal_confirmation']['pid']==r['child_pid']):
        raise RuntimeError('Missing owned terminal confirmation')
    terminal=r['terminal_confirmation']
    if (terminal['pid_requested']!=r['child_pid'] or terminal['code']!=os.CLD_EXITED or terminal['status']!=0
            or r['direct_wait_owner']!='runner wait4' or
            r['latest_decision_sample']['exit_lifecycle'].get('confirmation')!=terminal or
            not r['latest_decision_sample']['exit_lifecycle']['terminal_confirmed']):
        raise RuntimeError('Owned waitid/wait4 zero-status confirmation differs')
    if (r['memory_policy']['as_bytes']!=12*1024**3 or r['memory_policy']['file_size_bytes']!=64*1024**2
            or r['deadline_seconds']!=90): raise RuntimeError('Audit resource profile differs')
    limits={'RLIMIT_AS':[12*1024**3]*2,'RLIMIT_CPU':[60]*2,'RLIMIT_FSIZE':[64*1024**2]*2,'RLIMIT_CORE':[0,0]}
    if r['handshake']['limits']!=limits or not r['handshake']['lock_inheritable']:
        raise RuntimeError('Kernel limit/inherited-lock readback differs')
    if [r['lock']['device'],r['lock']['inode']]!=[33,3849]:raise RuntimeError('Receipt lock differs')
    handshake=r['handshake'];identity=r['child_identity']
    if ([handshake['lock_device'],handshake['lock_inode']]!=[33,3849] or
            handshake['lock_fd']!=r['lock']['fd'] or r['lock']['fd']!=lease['fd'] or
            handshake['pid']!=r['child_pid'] or handshake['ppid']!=r['supervisor_pid'] or
            handshake['sid']!=r['child_pid'] or handshake['pgid']!=r['child_pid'] or
            any(identity.get(k)!=v for k,v in {'pid':r['child_pid'],'stat_pid':r['child_pid'],
                'status_pid':r['child_pid'],'tgid':r['child_pid'],'ppid':r['supervisor_pid'],
                'sid':r['child_pid'],'pgid':r['child_pid']}.items()) or
            identity['start_ticks']!=r['tid_catalog'][str(r['child_pid'])]['start_ticks']):
        raise RuntimeError('Owned child/start-time/session/inherited-lock identity differs')
    if set(r['completed_logs'])!={'raw.log','samples.jsonl'}:raise RuntimeError('Raw/decision-log bindings incomplete')
    for name in ['admission','preexec_admission']:
        if r[name]['headroom']<4*1024**3 or r[name]['system_available']<3*1024**3:
            raise RuntimeError('Actual audit admission/preexec capacity failed')
    sample=E/'attempt/samples.jsonl'
    if not stat.S_ISREG(sample.lstat().st_mode) or sample.stat().st_size>DECISION_LIMIT:
        raise RuntimeError('Separate16MiB decision log bound failed')
    bindings=bind_outputs(r['audit_output_budget'])
    for name,row in r['completed_logs'].items():
        p=E/'attempt'/name
        if p.stat().st_size!=row['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256']:
            raise RuntimeError('Completed raw/decision log hash differs')
    raw=(E/'attempt/raw.log').read_text()
    if re.findall(r"option 'arena_reserve': ([0-9]+) KiB",raw)!=['131072']:
        raise RuntimeError('Official allocator option confirmation missing')
    result=validate_tables(Path(r['audit_output_budget']['work'])/'ci-evidence',plan['required_modules'],raw)
    return {'accepted_fresh_incremental_audit':True,'attempt_id':r['attempt_id'],
        'fresh_zero_exit':True,'final_preservation_matching':True,'outputs':bindings,
        **result,'provenance_upgrade':False,'dependency_cache_authentication':'unresolved',
        'full_clean_validation':'separate/unresolved','whole_paper_acceptance':False,
        'historical_counts_used_as_acceptance':False}
