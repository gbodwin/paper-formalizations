"""Preparation defaults to describe-only. Execution requires later explicit review authorization."""
from pathlib import Path
import hashlib, json, os, shutil, signal, stat, sys, traceback, uuid
from audit_context import A, R, PLAN, AuditContext, exact_command, reviewed_files
from audit_outputs import OUTPUTS, FILE_LIMIT, DISK_FLOOR
from audit_contract import chunk_file, reconcile_run
from shared_preservation import Lease, utc
from pilot_accounting import VisibleAccounting
import bootstrap_recovery
import child_runner as child


def save(path,data):
    temp=path.with_suffix('.tmp')
    with temp.open('w') as f:
        json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    temp.replace(path)


def preserve_outputs(ctx,evidence,state):
    target=evidence/'source-outputs';target.mkdir()
    for name in OUTPUTS:
        source=ctx.work/'ci-evidence'/name
        try:s=source.lstat()
        except FileNotFoundError:continue
        if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1 or s.st_size>FILE_LIMIT:
            state.setdefault('output_copy_findings',[]).append('Unsafe/oversize source output: '+str(source));continue
        fd=os.open(source,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
        with os.fdopen(fd,'rb') as src,(target/name).open('xb') as dst:
            shutil.copyfileobj(src,dst);dst.flush();os.fsync(dst.fileno())
        if hashlib.sha256(source.read_bytes()).digest()!=hashlib.sha256((target/name).read_bytes()).digest():
            raise RuntimeError('Preserved output copy mismatch')


def execute(reviewed_commit):
    # This function is deliberately not invoked in the preparation task.
    files=reviewed_files(reviewed_commit)
    with (A/'audit-invocation-claimed.json').open('x') as f:
        json.dump({'utc':utc(),'approved_adapter_commit':reviewed_commit,'one_invocation_only':True},f)
    run_id=uuid.uuid4().hex
    E=A/'executions'/run_id;E.mkdir(parents=True,exist_ok=False)
    W=R/'.lake'/('light-eft-full-audit-'+run_id)
    state={'status':'preparing','run_id':run_id,'approved_adapter_commit':reviewed_commit,
           'source_commit':PLAN['source_commit'],'no_automatic_retry':True,'attempts':0,
           'planned_Lean_invocations':1,'Lean_exec_authorized':False,
           'audit_accepted':False,'historical_counts_are_comparisons_only':True}
    state_path=E/'run-state.json';save(state_path,state)
    ctx=None;handlers={}
    for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGHUP]:
        handlers[sig]=signal.getsignal(sig)
        def interrupted(sig,frame):raise InterruptedError('Audit controller signal '+str(sig))
        signal.signal(sig,interrupted)
    try:
        lease=Lease(E/'batch-lock.json')
        with lease as lock:
            try:
                child.assert_idle('before-audit-preservation',state)
                if shutil.disk_usage(R).free<=DISK_FLOOR:raise RuntimeError('Fresh disk headroom must exceed2GiB')
                account=VisibleAccounting()
                state['initial_actual_capacity']=account.sample();save(state_path,state)
                state['bootstrap_idle_advice']=bootstrap_recovery.run_once(lock,account,E)
                ctx=AuditContext(lock,lease,E,W,reviewed_commit,files)
                state['fresh_output_spec']=ctx.output_spec;save(state_path,state)
                ctx.initialize()
                state.update(status='single-audit',canonical_inputs=ctx.input_ref,attempts=1);save(state_path,state)
                plan={'stage':'audit','module':'LightEFTFullAudit','argv':exact_command(),'env':PLAN['environment']}
                receipt=child.run_child(plan,W,E/'attempt',ctx,accounting=account)
                state['attempt_id']=receipt['attempt_id'];state['child_exit']=receipt['exit']
                state['Lean_exec_authorized']=bool(receipt.get('preexec_verified_ns'))
                state['status']='audit-child-completed-awaiting-final-preservation'
            except BaseException as exc:
                state.update(status='stopped-first-failure',controller_failure=repr(exc))
                traceback.print_exc()
                if (E/'attempt/receipt.json').exists():
                    receipt=json.loads((E/'attempt/receipt.json').read_text())
                    state['attempt_id']=receipt['attempt_id'];state['Lean_exec_authorized']=bool(receipt.get('preexec_verified_ns'))
            finally:
                # No retry or second Lean invocation can occur after this point.
                for sig in handlers:signal.signal(sig,signal.SIG_IGN)
                if ctx is not None and hasattr(ctx,'frozen'):
                    try:state['final_preservation']=ctx.final_verify()
                    except BaseException as exc:state['final_preservation_failure']=repr(exc);traceback.print_exc()
                else:state['final_preservation_failure']='No complete initial frozen input set; no audit acceptance'
                if ctx is not None:
                    try:preserve_outputs(ctx,E,state)
                    except BaseException as exc:state['output_copy_failure']=repr(exc);traceback.print_exc()
                save(state_path,state)
        # Lease release is verified by kernel ECHILD before acceptance parsing.
        try:
            result=reconcile_run(E,PLAN)
            if state.get('output_copy_findings') or state.get('output_copy_failure'):
                raise RuntimeError('Output copies incomplete/unsafe')
            for name in OUTPUTS:
                original=ctx.work/'ci-evidence'/name;copy=E/'source-outputs'/name
                if hashlib.sha256(original.read_bytes()).digest()!=hashlib.sha256(copy.read_bytes()).digest():
                    raise RuntimeError('Source/publication output hash differs')
            semantic_passed=True
        except BaseException as exc:
            result={'accepted_fresh_incremental_audit':False,'failure':repr(exc),'historical_counts_used_as_acceptance':False}
            state['reconciliation_failure']=repr(exc);semantic_passed=False
        # Export diagnostic chunks even on rejection; manifest acceptance labels
        # never replace the fresh execution/preservation/semantic conditions.
        exports=[]
        try:
            for source in sorted((E/'source-outputs').glob('*')) if (E/'source-outputs').exists() else []:
                exports.append(chunk_file(source,E/'audit-export'/source.name,PLAN['chunk_target_bytes']))
            raw=E/'attempt/raw.log'
            if raw.exists():exports.append(chunk_file(raw,E/'audit-export/raw.log',PLAN['chunk_target_bytes']))
            if semantic_passed and len(exports)!=5:raise RuntimeError('Four source outputs and raw output chunk exports required')
            state['audit_accepted']=semantic_passed
        except BaseException as exc:
            state['audit_accepted']=False;state['chunk_reconciliation_failure']=repr(exc)
        state['status']='fresh-incremental-audit-passed-awaiting-independent-review' if state['audit_accepted'] else 'audit-rejected-diagnostics-preserved'
        result['accepted_fresh_incremental_audit']=state['audit_accepted']
        result['row_aligned_chunk_reconstruction_verified']=state['audit_accepted']
        if state.get('chunk_reconciliation_failure'):result['chunk_failure']=state['chunk_reconciliation_failure']
        save(E/'audit-reconciliation.json',result)
        save(E/'audit-export-manifest.json',{'audit_accepted':state['audit_accepted'],'exports':exports})
    finally:
        for sig,handler in handlers.items():signal.signal(sig,handler)
        state['ended_utc']=utc();save(state_path,state)
    print(json.dumps({'evidence':str(E),'status':state['status'],'audit_accepted':state['audit_accepted']},indent=2))
    return 0 if state['audit_accepted'] else 1


def main(argv=None):
    argv=sys.argv[1:] if argv is None else argv
    if argv==['--execute-reviewed-audit']:
        raise SystemExit('Exact reviewed adapter commit argument required; no invocation started')
    if len(argv)==2 and argv[0]=='--execute-reviewed-audit':return execute(argv[1])
    if argv not in ([],['--describe']):raise SystemExit('Describe only, or later authorized --execute-reviewed-audit COMMIT')
    print(json.dumps({'status':'PREPARATION_ONLY_NOT_EXECUTED','argv':exact_command(),
        'review_required_before_execution':True,'planned_Lean_invocations':1,
        'executed_Lean_invocations_this_preparation':0},indent=2))
    return 0


if __name__=='__main__':raise SystemExit(main())
