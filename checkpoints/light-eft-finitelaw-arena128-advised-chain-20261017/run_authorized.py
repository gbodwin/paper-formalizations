"""Exactly one targeted advice pass followed by one fresh reviewed finite chain."""
from pathlib import Path
import datetime,json,traceback
import targeted_advice
import chain
BASE=Path(__file__).resolve().parent
if __name__=='__main__':
    with (BASE/'authorized-sequence-claimed.json').open('x') as f:json.dump({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'no_retry':True},f)
    status={'advice_invocations':0,'chain_invocations':0}
    try:
        status['advice_invocations']=1
        result=targeted_advice.run_once();print('Targeted advice completed: '+str(result['advice_calls'])+' files; current drop '+str(result['visible_current_drop_bytes'])+' bytes',flush=True)
        if result['state']!='completed':raise RuntimeError('Advice failed; chain forbidden')
        status['chain_invocations']=1;code=chain.main();status['chain_exit']=code
    except BaseException as exc:
        status['failure']=repr(exc);traceback.print_exc();code=1
    finally:
        status['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(BASE/'authorized-sequence-result.json').write_text(json.dumps(status,indent=2)+'\n')
    raise SystemExit(code)
