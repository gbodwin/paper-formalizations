"""Finite exact diagnostics only; not a theorem or active-regime counterexample."""
from itertools import product
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from chain_potential_model import analyze
import json,time

def instance(h):
    nodes=[''.join(p) for d in range(h+1) for p in product('01',repeat=d)]
    names=[('r',)]+[v for depth in reversed(range(h+1)) for u in nodes if len(u)==depth for v in [('x',u),('y',u)]]
    ix={v:i for i,v in enumerate(names)}
    edges={(ix[('x',u)],ix[('y',u)]) for u in nodes}
    for u in nodes:
        if len(u)==h:edges.add((0,ix[('x',u)]))
        if u:edges.add((ix[('y',u)],ix[('x',u[:-1])]))
        for d in range(1,len(u)):
            a=u[:d];b=a[:-1]+str(1-int(a[-1]));edges.add((ix[('y',u)],ix[('y',b)]))
    chains=[[0]]+[[ix[('x',u)],ix[('y',u)]] for u in nodes]
    return names,edges,chains

if __name__=='__main__':
    rows=[]
    for h in range(1,7):
        names,edges,chains=instance(h);start=time.time();r=analyze(len(names),edges,chains,greedy=True)
        r.update(h=h,n=len(names),chains=len(chains),seconds=time.time()-start,best_named=[names[v] for v in r['best_edge']] if r['best_edge'] else None)
        rows.append(r);print(json.dumps(r),flush=True)
    open(Path(__file__).with_name('finite-checks.json'),'w').write(json.dumps({'scope':'Exact finite empty-state all-candidate diagnostics only. No quantified theorem and no active-regime claim.','rows':rows},indent=2)+'\n')
