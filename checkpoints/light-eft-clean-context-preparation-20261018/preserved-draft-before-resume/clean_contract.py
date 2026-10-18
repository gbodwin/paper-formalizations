"""Data-only clean-context contracts. No process, network, extraction or advice API.

These validators model a later reviewed executor; they grant no execution
capability. Input metadata consistency is not artifact authentication.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, os, re

A=Path(__file__).resolve().parent
PLAN=json.loads((A/'PLAN.json').read_text())
GRAPH=json.loads((A/'frozen-graph.json').read_text())
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
class Rejected(ValueError):pass
class ProductionDisabled(RuntimeError):pass


def canonical(data):return json.dumps(data,sort_keys=True,separators=(',',':')).encode()
def digest(data):return hashlib.sha256(canonical(data)).hexdigest()
def require(ok,message):
    if not ok:raise Rejected(message)


def disabled_production(*args,**kwargs):
    raise ProductionDisabled('DISABLED: preparation only; no approval string, descriptor or override enables execution')


def path(text):
    p=PurePosixPath(text)
    require(p.is_absolute() and str(p)==text and '..' not in p.parts,'Noncanonical/relative path')
    return p


class CleanContext:
    """Pure fresh-path plan; construction creates no filesystem entry."""
    def __init__(self,run_id):
        require(bool(re.fullmatch('[0-9a-f]{32}',run_id)),'Fresh32hex run ID required')
        self.run_id=run_id
        self.root=PurePosixPath('/workspace/.lake')/('light-eft-clean-'+run_id)
        self.sources=self.root/'in/project-sources'
        self.dependencies=self.root/'in/dependency-objects'
        self.tool=self.root/'in/toolchain/lean4'
        self.helpers=self.root/'in/verified-helpers'
        self.objects=self.root/'out/project-objects'
        self.resolutions=self.root/'out/resolutions'
        self.work=self.root/'work'
        self.evidence=self.root/'evidence'
        self.input_id=digest({'source':SOURCE,'run':run_id,'pins':PLAN['pins'],'graph':digest(GRAPH)})
        self.output_id=digest({'run':run_id,'objects':str(self.objects),'resolutions':str(self.resolutions)})
    def object(self,module):return str(self.objects/PurePosixPath(*module.split('.')).with_suffix('.olean'))
    def resolution(self,module):return str(self.resolutions/(module+'.json'))
    def searches(self):
        return [str(self.objects)]+[str(self.dependencies/name/'lib/lean') for name in PLAN['pins']]+[str(self.tool/'lib/lean')]
    def environment(self,module,stage):
        env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_SYSROOT':str(self.tool),
             'LEAN_PATH':':'.join(self.searches()),'MIMALLOC_ARENA_RESERVE':'128MiB'}
        if stage in ('compile','audit'):env['MIMALLOC_VERBOSE']='1'
        if stage=='resolve':env.update(LIGHTEFT_CHECKER_TARGET=module,LIGHTEFT_CHECKER_RESOLUTION_FILE=self.resolution(module))
        if stage=='replay':env.update(LEAN_NUM_THREADS='1',LEAN_STACK_SIZE_KB='65536')
        return env
    def validate_start(self,facts):
        require(facts['root']==str(self.root) and not facts['root_preexisted'],'Historical/nonfresh root')
        require(facts['input_context']==self.input_id and facts['output_context']==self.output_id,'Wrong input/output context')
        require(not facts['project_object_files'] and not facts['resolution_files'],'Initial project ledgers must be empty')
        require(not facts['symlinks'] and not facts['historical_inputs'],'Symlink/historical-root input forbidden')
        require(facts['search_paths']==self.searches(),'Historical/shadow search root forbidden')
        require(facts['pins']==PLAN['pins'],'Wrong source pins')


def schedule():
    require(len(GRAPH)==486 and len({r['module'] for r in GRAPH})==486,'Wrong frozen graph')
    seen=set();result=[]
    for row in GRAPH:
        require(set(row['project_imports']).issubset(seen),'Not the frozen topological graph')
        module=row['module'];seen.add(module)
        stages=['compile'] if module=='LightEFTSpanners' else ['compile','resolve','replay']
        for stage in stages:result.append({'module':module,'stage':stage,'source_sha256':row['sha256']})
    require(GRAPH[-1]['module']=='LightEFTSpanners','Aggregate must compile last')
    result.append({'module':'LightEFTFullAudit','stage':'audit','source_sha256':PLAN['audit_source_sha256']})
    require(len(result)==1457 and len({(s['module'],s['stage']) for s in result})==1457,'Wrong/duplicate finite schedule')
    return result


def command(ctx,step):
    module=step['module'];stage=step['stage'];flags=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
    require(step in schedule(),'Stage outside fixed schedule; aggregate prefix replay forbidden')
    lean=str(ctx.tool/'bin/lean')
    if stage=='audit':return [lean,*flags,str(ctx.helpers/'LightEFTFullAudit.lean')]
    if stage=='resolve':return [lean,*flags,str(ctx.helpers/'LightEFTResolveCheckerTarget.lean')]
    if stage=='replay':return [str(ctx.tool/'bin/leanchecker'),'-v',module]
    row=next(r for r in GRAPH if r['module']==module)
    return [lean,*flags,'--root='+str(ctx.sources/row['srcDir']),'-o',ctx.object(module),str(ctx.sources/row['path'])]


def profile(stage):
    return 'audit' if stage=='audit' else 'ordinary'


def limits(stage):
    return {'RLIMIT_AS':[12*1024**3]*2,'RLIMIT_CPU':[60]*2,
            'RLIMIT_FSIZE':[(64 if stage=='audit' else 16)*1024**2]*2,'RLIMIT_CORE':[0,0]}


def validate_artifact_consistency(spec,authority):
    """Only consistency given an independently pinned review authority.

    The real authority in PLAN is None and the production descriptor remains
    UNAVAILABLE. Synthetic positive controls never activate production.
    """
    require(authority is not None,'No independently reviewed artifact authority')
    require(spec.get('status')=='REVIEWED_ARTIFACT','Unavailable artifact')
    require(spec['pins']==PLAN['pins'] and spec['toolchain']==PLAN['toolchain'],'Wrong artifact pins/toolchain')
    require(spec['lake_manifest_sha256']==PLAN['lake_manifest_sha256'],'Wrong manifest pin')
    require(spec['artifact_sha256']==authority['artifact_sha256'] and spec['bytes']==authority['bytes'],'Wrong artifact hash/size')
    require(digest(spec['files'])==authority['files_sha256'],'Wrong file inventory hash')
    provenance=spec['provenance']
    require(digest(provenance)==authority['provenance_sha256'],'Wrong/unreviewed provenance')
    require(provenance['official_archives']==3808 and provenance['official_origin_receipts_complete'] is True,
            'Incomplete official archive authentication')
    require(provenance['toolchain_distribution_authenticated'] is True and provenance['extractor_member_authenticated'] is True,
            'Distribution/extractor authentication missing')
    require(provenance['source_to_key_pins']==PLAN['pins'],'Provenance pins differ')
    require(re.fullmatch('[0-9a-f]{40}',authority['independent_review_commit']) is not None,'Unbound external review')
    files=spec['files'];require(len(files)==authority['file_count'] and len({f['relative_path'] for f in files})==len(files),'Incomplete/duplicate artifact inventory')
    for row in files:
        name=row['relative_path'];p=PurePosixPath(name)
        require(str(p)==name and not p.is_absolute() and '..' not in p.parts,'Unsafe artifact path')
        require(len(p.parts)>=4 and p.parts[0] in PLAN['pins'] and p.parts[1:3]==('lib','lean'),'Historical artifact root/layout')
        require(p.parts[3] not in ('LightEFTSpanners','LightSpanners') and not p.parts[3].startswith(('LightEFTSpanners.','LightSpanners.')),'Project object in dependency artifact')
        require(row['regular'] and not row['symlink'] and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'Nonregular/unbound artifact member')
    return {'metadata_consistent_with_supplied_authority':True,'production_enabled':False,'authentication_performed_here':False}


def validate_accounting(now,baseline,minimum):
    require(now['qualification']=='PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN','Bounded accounting qualification omitted')
    require(now['headroom']>=minimum and now['system_available']>=3*1024**3,'Admission capacity below profile')
    require(now['identities']==baseline['identities'],'Accounting identity changed')
    require(len(now['nodes'])==len(baseline['nodes']) and bool(now['nodes']),'Accounting nodes missing')
    for a,b in zip(now['nodes'],baseline['nodes']):
        require(a['path']==b['path'] and a['limit']==b['limit'] and a['oom']==b['oom'] and a['pids_events']==b['pids_events'],'OOM/PID/limit event changed')
    # No full-ancestor visibility predicate is added: unknown remains unknown.


def validate_receipt(ctx,step,frame):
    r=frame['receipt'];stage=step['stage'];module=step['module']
    require(r['state']=='finished' and r['exit']==0 and not r.get('failure'),'Fresh successful receipt required')
    require(r['source_commit']==SOURCE and r['stage']==stage and r['module']==module,'Wrong exact source/stage')
    require(r['argv']==command(ctx,step) and r['environment']==ctx.environment(module,stage),'Wrong command/environment or historical root')
    require(r['clean_input_context']==ctx.input_id and r['clean_output_context']==ctx.output_id,'Cross-context receipt')
    source_hash=PLAN['resolver_source_sha256'] if stage=='resolve' else step['source_sha256']
    require(r['submitted_source_sha256']==source_hash,'Wrong submitted source hash')
    require(r['supervisor_profile']==profile(stage) and r['handshake']['limits']==limits(stage),'Resource profiles mixed')
    require(r['deadline_seconds']==90 and r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone'],'Deadline/cleanup mismatch')
    require(r['direct_wait_owner']=='runner wait4' and r['waitid_wait4_status_match'],'Unowned/mismatched reaping')
    c=r['terminal_confirmation'];pid=r['child_pid'];ident=r['child_identity']
    require(c['terminal'] and c['pid']==pid and c['pid_requested']==pid and c['status']==0 and c['code']==os.CLD_EXITED,'Unowned terminal receipt')
    require(all(ident[k]==v for k,v in {'pid':pid,'stat_pid':pid,'status_pid':pid,'tgid':pid,'ppid':r['supervisor_pid'],'sid':pid,'pgid':pid}.items()) and ident['start_ticks']>0,'Child identity mismatch')
    require(r['lock']['device']==33 and r['lock']['inode']==3849 and r['handshake']['lock_inheritable'],'Common lock mismatch')
    h=r['handshake']
    require(h['pid']==pid and h['ppid']==r['supervisor_pid'] and h['sid']==pid and h['pgid']==pid and
            h['lock_device']==33 and h['lock_inode']==3849 and h['lock_fd']==r['lock']['fd'],'Handshake ownership/lock differs')
    require(r['lock']['outer_acquired_ns']<=r['started_ns']<r['ended_ns'],'Not under lease')
    minimum=(4 if stage in ('replay','audit') else 3)*1024**3
    for name in ['admission','preexec_admission']:validate_accounting(r[name],r['admission'],minimum)
    require(r['disk_admission_bytes']>2*1024**3 and r['disk_preexec_bytes']>2*1024**3,'Fresh disk below boundary')
    require(r['decision_log_bytes']<=16*1024**2,'Decision log enlarged')
    for s in frame['runtime_samples']:
        require(s['visible_headroom']>=1024**3 and s['host_available']>=1024**3,'Runtime physical-memory floor')
        require(s['shared_mm_rss']<6*1024**3 and all(v<3*1024**3 for v in s['anon_growth_by_cgroup'].values()),'RSS/anonymous stop')
    p=frame['preservation']
    require(p['all_paths_attempted'] and p['paths_checked']==p['input_count'] and p['input_count']>0,'Incomplete stage preservation')
    require(p['before_sha256']==p['after_sha256']==r['canonical_input_inventory']['sha256'],'Stage input mutation')
    require(p['input_context']==ctx.input_id,'Wrong preservation context')


class DryRunLedger:
    """Synthetic/static state machine, not a producer of actual validation evidence."""
    def __init__(self,ctx):
        self.ctx=ctx;self.steps=schedule();self.position=0;self.stopped=False
        self.provisional_objects={};self.provisional_resolutions={};self.accepted_objects={};self.accepted_resolutions={}
        self.quarantined_outputs=[];self.failures=[];self.receipts=[];self.ids=set();self.pids=set();self.last_end=0
        self.input_sha256=None;self.input_count=None;self.finalized=False;self.last_frame=None
    def consume(self,frame):
        require(not self.stopped and not self.finalized,'Stopped/finalized: no automatic retry')
        try:
            require(self.position<len(self.steps),'Duplicate/extra stage')
            step=self.steps[self.position];r=frame['receipt'];validate_receipt(self.ctx,step,frame)
            p=frame['preservation']
            if self.input_sha256 is None:self.input_sha256=p['before_sha256'];self.input_count=p['input_count']
            require(p['before_sha256']==self.input_sha256 and p['input_count']==self.input_count,'Frozen input inventory changed across stages')
            require(r['attempt_id'] not in self.ids and (r['child_pid'],r['child_identity']['start_ticks']) not in self.pids,'Duplicate attempt/identity')
            require(r['started_ns']>self.last_end,'Overlapping stage')
            module=step['module'];stage=step['stage']
            if stage=='compile':
                obj=frame['output']
                require(module not in self.provisional_objects and obj['path']==self.ctx.object(module),'Stale/wrong object path')
                require(obj['module']==module and obj['source_sha256']==step['source_sha256'],'Object source differs')
                require(obj['context']==self.ctx.output_id and obj['producer_attempt']==r['attempt_id'] and obj['fresh'] and obj['regular'] and not obj['symlink'],'Historical/partial object provenance')
                require(re.fullmatch('[0-9a-f]{64}',obj['sha256']) is not None,'Unbound object hash')
                self.provisional_objects[module]=dict(obj)
            elif stage=='resolve':
                obj=self.provisional_objects.get(module);res=frame['resolution']
                require(obj is not None,'No successful fresh compilation')
                expected=[{'module':module,'object':obj['path']}]
                require(res['target']==module and res['count']==1 and res['resolved']==expected,'Wrong/shadow/prefix resolution')
                require(res['path']==self.ctx.resolution(module) and res['context']==self.ctx.output_id and res['fresh'],'Stale resolution context')
                require(res['object_sha256']==obj['sha256'] and frame['search_hits']==expected,'Stale/shadowed object hash')
                self.provisional_resolutions[module]=dict(res)
            elif stage=='replay':
                obj=self.provisional_objects.get(module);res=self.provisional_resolutions.get(module)
                require(obj is not None and res is not None,'Replay before fresh compile/resolution')
                require(frame['resolution']==res and frame['object_sha256']==obj['sha256'],'Replay object/resolution changed')
                require(frame['raw_output']=='replaying '+module+'\n','Not exact singleton replay')
            else:
                require(len(self.provisional_objects)==486 and len(self.provisional_resolutions)==485,'Audit before full fresh schedule')
            self.ids.add(r['attempt_id']);self.pids.add((r['child_pid'],r['child_identity']['start_ticks']));self.last_end=r['ended_ns'];self.receipts.append(r);self.position+=1
            self.last_frame=frame
        except (Rejected,KeyError,TypeError) as error:
            self.quarantined_outputs.extend(frame.get('partial_outputs',[]))
            if frame.get('output'):self.quarantined_outputs.append(frame['output'])
            self.stopped=True;self.failures.append(str(error));raise
    def finalize(self,final_preservation,audit_files,chunk_exports):
        try:
            require(not self.stopped and not self.finalized and self.position==1457 and not self.failures,'Incomplete/failed finite run')
            require(final_preservation['all_paths_attempted'] and final_preservation['matching'] and
                    final_preservation['paths_checked']==final_preservation['input_count'] and
                    final_preservation['before_sha256']==final_preservation['after_sha256']==self.input_sha256 and
                    final_preservation['input_count']==self.input_count,'Incomplete final preservation')
            from audit_data import reconcile_audit_data
            audit=reconcile_audit_data(self.ctx,self.last_frame,audit_files,chunk_exports)
            require(final_preservation['input_context']==self.ctx.input_id,'Wrong final context')
            self.accepted_objects=dict(self.provisional_objects);self.accepted_resolutions=dict(self.provisional_resolutions)
            self.finalized=True
            return {'synthetic_contract_gates_satisfied':True,'actual_clean_validation_performed':False,'production_enabled':False,'audit':audit}
        except (Rejected,KeyError,TypeError) as error:
            self.stopped=True;self.failures.append(str(error));raise
