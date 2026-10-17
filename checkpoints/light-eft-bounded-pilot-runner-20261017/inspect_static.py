"""Read-only inventory/accounting checks; never calls run_once or starts Lean."""
import json
from pathlib import Path
import pilot_runner as r
from pilot_accounting import VisibleAccounting
acc=VisibleAccounting();first=acc.sample();second=acc.sample();acc.expected['namespace']='intentional fixture mismatch'
try:acc.sample()
except RuntimeError as e:rejected=str(e)
else:raise AssertionError('identity change accepted')
paths=r.production_inputs(r.PILOT/'ImportSmoke.lean')
result={'official_lean_sha256_matches':r.digest(r.LEAN)['sha256']==r.LEAN_SHA,'input_paths_count':len(paths),'input_total_existing_bytes':sum(f.stat().st_size for f in paths if f.exists()),'env':r.environment(),'pilot_directory_not_created':not r.PILOT.exists(),'evidence_directory_not_created':not r.EVIDENCE.exists(),'existing_accounting_observation':first,'second_observation_headroom':second['headroom'],'intentional_identity_change_rejected':rejected,'lean_invocations':0}
(r.HERE/'evidence/static-production-plan.json').write_text(json.dumps(result,indent=2)+'\n')
print('Read-only accounting and identity-change refusal pass. Inventory paths:',len(paths),'bytes:',result['input_total_existing_bytes'],'No Lean.')
