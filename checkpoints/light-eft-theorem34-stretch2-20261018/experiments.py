"""Exact-rational finite stretch-2 experiments; not Lean/compiler/kernel checks."""
from pathlib import Path
from fractions import Fraction as R
from itertools import combinations
import heapq,json,random

A=Path(__file__).resolve().parent
def edge(u,v):return (min(u,v),max(u,v))
def dist(n,weights,F,source):
    adj=[[] for _ in range(n)]
    for (u,v),w in weights.items():
        if (u,v) not in F:adj[u].append((v,w));adj[v].append((u,w))
    d=[None]*n;d[source]=R(0);heap=[(R(0),source)]
    while heap:
        cost,u=heapq.heappop(heap)
        if d[u]!=cost:continue
        for v,w in adj[u]:
            new=cost+w
            if d[v] is None or new<d[v]:d[v]=new;heapq.heappush(heap,(new,v))
    return d

def shape(f,q,t):
    s=q+1;r=2*t;cuts=[]
    for x in range(r+1):
        for y in range(s+1):
            if (x,y) in [(0,0),(r,s)]:continue
            count=x*(s-y)+(r-x)*y;assert count>=s
            cuts.append({'terminals_in_cut':x,'hubs_in_cut':y,'crossing_edges':count})
    # Each possible subset has exactly one of these cardinality pairs.
    return {'f':f,'q':q,'t':t,'n':r+s,'all_cut_cardinality_pairs':cuts}

def case(f,q,t,h,a):
    s=q+1;r=2*t;n=r+s;b=R(3,2)
    Q={edge(u,r+j):(a if j<h else b) for u in range(r) for j in range(s)}
    heavy={edge(u,v):R(1) for u in range(t) for v in range(t,2*t)}
    G=Q|heavy;S=h*a+(s-h);T=h*a+(s-h)*b
    assert sum(Q.values())==2*t*T
    # Terminal incident-cost screen from accepted Lemma A.
    for u in range(r):
        cheapest=sorted(w for e,w in G.items() if u in e)[:s]
        assert sum(cheapest)==S
    denominator_lower=t*S;witnesses=[]
    if 2*h<=f:
        H=G;factor=R(2);phase='all heavy edges forced, costly denominator'
        for e in heavy:
            u,v=e;F={edge(z,r+j) for z in e for j in range(h)}
            assert len(F)==2*h<=f and e not in F
            de=dist(n,{k:w for k,w in G.items() if k!=e},F,u)[v]
            dg=dist(n,G,F,u)[v]
            assert dg==1 and de is not None and de>2
            witnesses.append({'edge':list(e),'faults':[list(x) for x in sorted(F)],'alternative_distance':str(de)})
        assert sum(H.values())/denominator_lower<=R(4*t,3*s)+3
    elif h<=f:
        H=dict(Q);factor=R(2);phase='representative heavy edges give constant-ratio spanner'
        a0=set(range(f+1));b0=set(range(t,t+f+1))
        H.update({e:w for e,w in heavy.items() if e[0] in a0 or e[1] in b0})
        assert sum(H.values())/denominator_lower<=5
    else:
        H=Q;factor=R(1);phase='cheap hubs already give exact fault distance preservation'
        assert sum(H.values())/denominator_lower<=3
    checked=0;fault_scope='not needed: H=G; explicit forcing sets checked';worst=R(1)
    if H!=G:
        E=sorted(G);faults=[frozenset()]+[frozenset([e]) for e in E]
        if f==1:fault_scope='exhaustive over every input-edge F of size at most 1'
        else:
            rng=random.Random(3402);faults += [frozenset(rng.sample(E,2)) for _ in range(32)]
            faults=list(dict.fromkeys(faults));fault_scope='empty, all singleton faults and 32 deterministic sampled two-edge faults; not exhaustive'
        for F in faults:
            assert len(F)<=f
            for u in range(n):
                dg=dist(n,G,F,u);dh=dist(n,H,F,u)
                for v in range(n):
                    assert dg[v] is not None and dh[v] is not None
                    assert dh[v]<=factor*dg[v],(f,h,a,F,u,v,dh[v],dg[v])
                    if u!=v:worst=max(worst,dh[v]/dg[v])
            checked+=1
    return {'f':f,'q':q,'t':t,'h':h,'a':str(a),'b':str(b),'phase':phase,'certificate_weight':str(2*t*T),
      'proved_denominator_lower_bound':str(denominator_lower),'eligible_output_weight':str(sum(H.values())),
      'competitive_ratio_upper_bound':str(sum(H.values())/denominator_lower),'spanner_factor_tested':str(factor),
      'all_pairs_fault_sets_checked':checked,'fault_scope':fault_scope,'maximum_observed_stretch':str(worst),
      'forcing_witnesses':witnesses}

if __name__=='__main__':
    shapes=[shape(1,2,4),shape(2,4,6)];cases=[]
    for f,q,t in [(1,2,4),(2,4,6)]:
        for a in [R(1,4),R(1,4*(f+1)**2)]:
            for h in range(q+2):cases.append(case(f,q,t,h,a))
    result={'scope':'Exact finite experiments only; no arbitrary-parameter formal acceptance',
      'shapes':shapes,'cases':cases,'all_cut_types_checked':sum(len(s['all_cut_cardinality_pairs']) for s in shapes),
      'forcing_witnesses_checked':sum(len(c['forcing_witnesses']) for c in cases),
      'all_pairs_fault_sets_checked':sum(c['all_pairs_fault_sets_checked'] for c in cases),
      'original_theorem_status':'OPEN; candidate-family obstruction only'}
    (A/'experiment-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'cases':len(cases),'all_cut_types_checked':result['all_cut_types_checked'],
      'forcing_witnesses_checked':result['forcing_witnesses_checked'],'all_pairs_fault_sets_checked':result['all_pairs_fault_sets_checked'],
      'sampled_cases_are_not_exhaustive':True,'status':'all finite assertions passed'},indent=2))
