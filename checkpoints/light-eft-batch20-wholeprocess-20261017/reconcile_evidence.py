"""Offline reconciliation only; no Lean, advice, fixture rerun or third input pass."""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import re
import subprocess

B=Path(__file__).resolve().parent
R=B.parents[1]


def load(p):return json.loads(p.read_text())


def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()


def main():
    state=load(B/'batch-result.json');plan=load(B/'PLAN.json');final=load(B/'final-content-verification.json');lease=load(B/'batch-lock.json')
    accepted=['LightEFTSpanners.AdaptiveFiniteLaw','LightEFTSpanners.FiniteHoeffding']
    assert state['accepted_modules']==state['provisional_modules']==accepted
    assert state['status']=='stopped-first-failure' and len(state['stages'])==7
    assert final['matching'] and final['all_paths_attempted'] and not final['changes'] and final['paths_checked']==74615
    assert sha(B/'inputs.jsonl')==final['before_sha256']==final['after_stream_sha256']=='c6ef74001a7bcbf35624556862f87e173ff939863d85631e253686815ad450cd'
    assert lease['state']=='released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns']<final['started_ns']<final['ended_ns']<lease['release_verified_ns']
    records=[];receipts=[];catalogs=[]
    for item in state['stages']:
        path=B/item['receipt'];r=load(path);receipts.append(r)
        assert r['source_commit']==plan['source_commit'] and r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
        assert r['between_child_preservation_passed'] and r['canonical_input_inventory']['sha256']==final['before_sha256']
        assert r['lock']['outer_acquired_ns']==lease['acquired_ns'] and (r['lock']['device'],r['lock']['inode'])==(33,3849)
        assert sha(B/r['source_snapshot'])==r['submitted_source_sha256']
        assert r['handshake']['limits']=={'RLIMIT_AS':[12884901888,12884901888],'RLIMIT_CPU':[60,60],'RLIMIT_FSIZE':[16777216,16777216],'RLIMIT_CORE':[0,0]}
        assert r['exit']==0
        raw=(path.parent/'raw.log').read_text();warnings=len(re.findall(r'^.*\.lean:\d+:\d+: warning:',raw,re.M));assert warnings==0
        ss=[json.loads(x) for x in (path.parent/'samples.jsonl').read_text().splitlines()]
        assert ss[-1]==r['latest_decision_sample']
        if r['state']=='finished':
            assert r['waitid_wait4_status_match'] and r['terminal_confirmation']['terminal'] and r['terminal_confirmation']['status']==0
            if r['stage']=='replay':assert raw=='replaying '+r['module']+'\n'
            if r.get('process_teardown'):assert r['process_teardown']['confirmed_ns']<=r['process_teardown']['deadline_ns']
        for sample in ss:
            m=sample.get('process_memory',{})
            if m.get('source_tid') is not None:
                assert m['tgid']==r['child_pid'] and m['start_ticks']==r['tid_catalog'][str(m['source_tid'])]['start_ticks']
                assert sample['exit_lifecycle']['live_lock_verification']['tid']==m['source_tid']
                assert m['aggregation'].endswith('never summed')
        records.append({'module':r['module'],'stage':r['stage'],'attempt_id':r['attempt_id'],'receipt':item['receipt'],
                        'source_sha256':r['submitted_source_sha256'],'child_pid':r['child_pid'],'exit':r['exit'],'state':r['state'],
                        'created_utc':r['created_utc'],'ended_utc':r['ended_utc'],'failure':r.get('failure'),
                        'argv':r['argv'],'environment':r['environment'],'sample_count':len(ss),'sampled_rss_peak_bytes':r['sampled_rss_peak_bytes'],
                        'wait4_rss_bytes':r['wait4_maxrss_kib']*1024,'admission_visible_bytes':r['admission']['headroom'],
                        'preexec_visible_bytes':r['preexec_admission']['headroom'],'minimum_runtime_visible_bytes':min(x['accounting']['headroom'] for x in ss),
                        'retained_tids':len(r['tid_catalog']),'live_sibling_samples':sum(bool(x['exit_lifecycle'].get('using_live_sibling_memory')) for x in ss),
                        'teardown_pending_samples':sum(bool(x['exit_lifecycle'].get('teardown_pending')) for x in ss),'lean_warning_headers':warnings})
        catalogs.append({'module':r['module'],'stage':r['stage'],'attempt_id':r['attempt_id'],'tid_catalog':r['tid_catalog'],'process_teardown':r.get('process_teardown')})
    assert all(a['ended_ns']<b['lock']['child_entry_ns'] for a,b in zip(receipts,receipts[1:]))
    assert len({x['attempt_id'] for x in receipts})==7
    assert sum(x['stage']=='compile' for x in receipts)==2
    assert all(x['module'] not in {s['module'] for s in plan['accepted_seeds']} for x in receipts if x['stage']=='compile')
    failed=receipts[-1];stop=failed['stop_decision_sample'];fresh=stop['child']['fd_transition_reread']
    assert failed['state']=='failed' and failed['module']=='LightEFTSpanners.ProductSampleConcentration'
    assert stop==failed['latest_decision_sample']
    assert stop['child']['rss'] is not None and stop['child']['state']=='S'
    assert fresh['rss'] is None and fresh['vm'] is None and fresh['stat_flags']&4 and fresh['stat_vsize_bytes']==fresh['stat_rss_pages']==0
    assert fresh['tgid']==failed['child_pid'] and fresh['start_ticks']==stop['child']['start_ticks']
    assert all(not p['terminal'] for p in stop['exit_lifecycle']['probes']) and not stop['exit_lifecycle']['terminal_confirmed']
    assert stop['process_memory']['rss'] is None and failed['memory_stop_signal_sent']
    assert all(x.get('known_tid_positively_gone') for x in stop['exit_lifecycle']['threads'][1:])
    latest=max([stop['sample_finished_ns'],fresh['tid_read_finished_ns']]+[p['finished_ns'] for p in stop['exit_lifecycle']['probes']])
    assert latest<=failed['memory_stop_signal_started_ns']<failed['process_teardown']['deadline_ns']
    assert failed['stop_decision_errors']==["{'operation': 'whole-process supervision', 'error': 'No identity-checked live shared-mm telemetry or bounded exiting-only group'}"]
    (B/'product-resolver-stop-sample.json').write_text(json.dumps(stop,indent=2)+'\n')
    (B/'thread-catalogs.json').write_text(json.dumps(catalogs,indent=2)+'\n')
    phases={(r['module'],r['stage']):r for r in receipts};statuses=[]
    for i,row in enumerate(plan['modules']):
        entry={'module':row['module'],'accepted':row['module'] in accepted,'source_sha256':row['sha256']}
        for phase in ['compile','resolve','replay']:
            r=phases.get((row['module'],phase))
            entry[phase]='reused_prior_accepted_compilation' if i==0 and phase=='compile' else ('passed' if r and r['state']=='finished' else 'failed_closed' if r else 'skipped_after_first_failure')
        statuses.append(entry)
    (B/'module-status.json').write_text(json.dumps(statuses,indent=2)+'\n')
    ledger=json.loads((B/'output-records.jsonl').read_text().splitlines()[-1]);assert len(ledger['objects'])==4
    for row in ledger['objects']:
        path=Path(row['path']);copy=B/'preserved-objects'/path.relative_to(path.parents[1])
        assert sha(path)==sha(copy)==row['sha256']
    fixture_rows=load(B/'whole-process-fixture-results.json')['cases'];assert len(fixture_rows)==14 and all(x['passed'] for x in fixture_rows)
    for case in fixture_rows:
        r=load(B/case['receipt']);l=load(B/case['folder']/'lease.json')
        assert r['fixture_only'] and not r['compiler_or_checker'] and r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
        assert l['state']=='released' and l['kernel_echild_at_release']
        for name,digest in r['harness_hashes'].items():assert sha(B/name)==digest
    scope=Counter();scope_digest=hashlib.sha256();scope_bytes=0
    with (B/'inputs.jsonl').open() as f:
        for line in f:
            row=json.loads(line)
            if row['advice_scope']:
                scope[row['advice_scope']]+=1;scope_bytes+=row['bytes'];scope_digest.update((json.dumps({'path':row['path'],'identity':row['identity']},separators=(',',':'))+'\n').encode())
    assert scope=={'previously_accepted_evidence_data':7129,'reviewed_dependency_or_tool_object':66961} and scope_bytes==11790867848
    bootstrap=load(B/'bootstrap-recovery.json');assert bootstrap['state']=='completed' and bootstrap['counts']==dict(scope)
    assert bootstrap['scope_identity_sha256']==scope_digest.hexdigest()
    idle=[json.loads(x) for x in (B/'cache-advice.jsonl').read_text().splitlines()]
    for x in idle:assert x['state']=='completed' and x['counts']==dict(scope) and x['scope_identity_sha256']==scope_digest.hexdigest()
    result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Offline reconciliation; no third full frozen-input hash or further tool/advice attempts',
            'source_commit':plan['source_commit'],'result':'TWO_QUALIFIED_MODULE_CHAINS_PASSED_PRODUCT_RESOLVER_BOOKKEEPING_STOP',
            'accepted_modules':accepted,'planned_remaining_stages':59,'attempted_stages':7,'skipped_stages':52,
            'compiler_invocations':2,'resolver_invocations':3,'checker_invocations':2,'accepted_seed_recompilations':0,
            'stages':records,'canonical_inventory':state['canonical_inputs'],'final_full_content_verified':True,'full_content_pass_count':2,
            'one_shared_lock_through_final_verification':True,'nonoverlap':True,'all_children_reaped':True,
            'focused_fixture_cases_passed':14,'scope_not_expanded':True,'advice_scope_counts':dict(scope),'advice_bytes_per_pass':scope_bytes,
            'pre_initial_idle_passes':1,'between_child_idle_passes':len(idle),'bootstrap_measured_visible_drop_bytes':bootstrap['visible_current_drop_bytes'],
            'output_records':ledger,'new_recursive_axiom_audits':0,'new_ci_runs':0,
            'remaining_blocker':'FD-to-no-mm re-read starts grace but the final fallback still classifies the earlier live leader row; generic false stop before grace can continue. No post-failure repair/retry.'}
    (B/'result-reconciliation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('stages','output_records')},indent=2))


if __name__=='__main__':main()
