"""Verify recorded process continuity and rewrite current derived disconnect evidence; no Lean execution."""
from pathlib import Path
import json,hashlib
b=Path('checkpoints/light-eft-edge-membership-contains-pilot-20261016/evidence');d=json.loads((b/'disconnect-reconciliation.json').read_text());snap=d['latest_receipt_snapshot'];p=b/'attempts'/snap['attempt_id']/'receipt.json';final=json.loads(p.read_text())
keys=['argv','attempt_id','child_pid','cwd','label','lean_environment','lock_device','lock_inode','lock_path','preflight_sha256','process_group','submitted_sources','supervisor_pid','start_monotonic_ns','start_utc']
assert all(snap[k]==final[k] for k in keys)
assert final['exit']==0 and final['child_reaped'] and final['supervisor_pid']==103353
rs=[json.loads(p.read_text()) for p in (b/'attempts').glob('*/receipt.json')]
build=[r for r in rs if r['label'].startswith('fresh-compile-') and r['label']!='fresh-compile-LightEFTSpanners.StoredEdgeMembership']
assert len(build)==175 and {r['supervisor_pid'] for r in build}=={103353} and all(r['exit']==0 and r['child_reaped'] for r in build)
r=dict(original_session=88395,supervisor_pid=103353,main_build_compilations=175,separate_initial_pilot_compile=1,observed_running_attempt=snap['attempt_id'],observed_child_pid=snap['child_pid'],final_receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),snapshot_identity_fields_match=keys,observed_child_completed_and_reaped=True,all_main_build_receipts_same_supervisor=True,qualification='Reconciles preserved observations with final recorded receipts; not proof against unrecorded execution.')
(b/'disconnect-final-reconciliation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
