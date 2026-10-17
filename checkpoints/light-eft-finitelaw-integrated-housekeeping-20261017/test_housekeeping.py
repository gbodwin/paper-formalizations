"""Focused harmless checks; no compiler/checker or production history advice."""
from pathlib import Path
import hashlib,json,os
from unittest.mock import patch
import integrated_housekeeping as h
BASE=Path(__file__).resolve().parent
work=BASE/'harmless-test-work';work.mkdir(exist_ok=False)
fixture=work/'fixture.txt';fixture.write_bytes(b'preserved fixture bytes\n')
row={'path':str(fixture),'bytes':fixture.stat().st_size,'sha256':hashlib.sha256(fixture.read_bytes()).hexdigest()}
results={}
with patch.object(h.os,'posix_fadvise') as advice:
    try:h.advise_historical(row,{})
    except RuntimeError as exc:results['whitelist_rejection']=str(exc)=='Not a pinned whitelist member' and not advice.called
bad={**row,'sha256':'0'*64}
with patch.object(h.os,'posix_fadvise') as advice:
    try:h.advise_historical(bad,{str(fixture):bad})
    except RuntimeError:results['hash_mismatch_before_advice']=not advice.called
assert fixture.read_bytes()==b'preserved fixture bytes\n'
new=work/'evidence/compile/inputs-before.json';new.parent.mkdir(parents=True)
record={};events=[];real_sync=os.fsync;real_hash=hashlib.file_digest;real_advice=os.posix_fadvise
with patch.object(h,'HERE',work),patch.object(h.os,'fsync',side_effect=lambda fd:(events.append('fsync'),real_sync(fd))[1]),patch.object(h.hashlib,'file_digest',side_effect=lambda *a,**k:(events.append('hash'),real_hash(*a,**k))[1]),patch.object(h.os,'posix_fadvise',side_effect=lambda *a:(events.append('advice'),real_advice(*a))[1]):
    entry=h.write_inventory([{'fixture':'unchanged'}],new,record,lambda:None)
expected=(json.dumps([{'fixture':'unchanged'}],indent=2)+'\n').encode()
results['evidence_preserved_same_fd']=new.read_bytes()==expected and entry['identity']==entry['identity_after_advice'] and events==['fsync','hash','advice']
order=[];state={}
class Accounting:
    def sample(self):order.append('sample');return {'fresh':True}
with patch.object(h,'write_inventory',side_effect=lambda *a:(order.append('inventory'),{'sha256':'fixture'})[1]),patch.object(h,'complete_one',side_effect=lambda *a:order.append('preflight-log')),patch.object(h,'run_history_once',side_effect=lambda *a:order.append('history')):
    h.admit_after_preflight(work,[], 'compile',-1,Accounting(),state,lambda:None,lambda now:order.append('gate'))
results['production_ordering']=order==['inventory','preflight-log','history','sample','gate'] and state['preflight_order']==['input-verification-completed','new-preflight-files-fsynced-hashed-advised','single-history-pass-completed','fresh-admission-sampled','admission-passed']
assert all(results.values()),results
(BASE/'harmless-tests.json').write_text(json.dumps({'checks':results,'ordering':order,'same_fd_finish_order':events,'scope':'Fixtures preserved; no compiler/checker and no production history pass'},indent=2)+'\n')
print(json.dumps(results,indent=2))
