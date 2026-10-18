"""Small exact-rational graph experiments, not Lean/compiler/kernel checks.

The arbitrary-parameter mathematical proofs are in REPORT.md. Exhaustive finite
instances here do not replace those proofs or establish the general theorem.
"""
from fractions import Fraction as R
from itertools import combinations
from math import comb,isqrt
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
def connected(n,edges,faults):
    adj=[[] for _ in range(n)]
    for i,j in edges:
        if (i,j) not in faults:adj[i].append(j);adj[j].append(i)
    seen={0};todo=[0]
    while todo:
        v=todo.pop()
        for u in adj[v]:
            if u not in seen:seen.add(u);todo.append(u)
    return len(seen)==n

def distances(n,weights,faults):
    d=[[None]*n for _ in range(n)]
    for v in range(n):d[v][v]=R(0)
    for e,w in weights.items():
        if e not in faults:i,j=e;d[i][j]=d[j][i]=w
    for k in range(n):
        for i in range(n):
            if d[i][k] is None:continue
            for j in range(n):
                if d[k][j] is None:continue
                candidate=d[i][k]+d[k][j]
                if d[i][j] is None or candidate<d[i][j]:d[i][j]=candidate
    return d

def two_blocks(N,q,f):
    n=2*N;delta=R(1,N*(N-1));all_edges=list(combinations(range(n),2))
    weights={e:(delta if (e[0]<N)==(e[1]<N) else R(1)) for e in all_edges}
    certificate={e:w for e,w in weights.items() if (e[0]<N)==(e[1]<N)}
    for i in range(q+1):certificate[i,N+i]=R(1)
    assert sum(certificate.values())==q+2
    # Every actual input-edge fault set, including faults outside Q.
    faults_checked=0
    for size in range(q+1):
        for fs in combinations(all_edges,size):
            F=set(fs);assert connected(n,certificate,F);assert connected(n,weights,F);faults_checked+=1
    assert faults_checked==sum(comb(len(all_edges),i) for i in range(q+1))
    for u in range(N):
        for v in range(N,2*N):
            d=distances(n,weights,{(u,v)})
            assert d[u][v]==1+delta>1
    stretch=1+4*delta;spanner_faults=0;worst=R(1)
    for size in range(f+1):
        for fs in combinations(all_edges,size):
            F=set(fs);dg=distances(n,weights,F);dq=distances(n,certificate,F)
            for u in range(n):
                for v in range(n):
                    assert dg[u][v] is not None and dq[u][v] is not None
                    assert dq[u][v]<=stretch*dg[u][v]
                    if u!=v:worst=max(worst,dq[u][v]/dg[u][v])
            spanner_faults+=1
    # Here cf=q exactly. The report treats general real cf analytically.
    M=isqrt(n*n//q);lambda_upper=R(M*(M-1),2)
    assert R(N*N,q+2)>=lambda_upper/4
    return {'N':N,'n':n,'q':q,'f':f,'delta':str(delta),'certificate_weight':q+2,
      'denominator_interval_proved_in_notes':[q+1,q+2],'all_input_fault_sets_connectivity_checked':faults_checked,
      'all_input_fault_sets_distance_checked':spanner_faults,'missing_heavy_edges_tested':N*N,
      'stated_spanner_stretch':str(stretch),'maximum_observed_stretch':str(worst),
      'rounded_extremal_order':M,'lambda_M_2_upper_bound':str(lambda_upper),
      'stretch_1_ratio_lower_bound':str(R(N*N,q+2))}

def quantile_obstruction():
    cases=[]
    for p in [3,5,7,9]:
        q=p*p-1;f=q//2
        for m in range(p+1,51):
            cheapest=sum(sum(sorted(abs(u-v)+1 for v in range(m) if u!=v)[:p]) for u in range(m))
            actual_degree_bound=R(p*p*cheapest,2)
            closed_bound=R(m*p**3*(p+5),8)
            assert actual_degree_bound>=closed_bound
            base_weight=R(m*(m-1)*(m+4),6);mst=2*(m-1);base_lightness=base_weight/mst
            lift_weight=p*p*base_weight
            ratio_upper=lift_weight/closed_bound
            relative_upper=R(16*(m-1),m*p*(p+5))
            assert ratio_upper/base_lightness==relative_upper
            assert R(4*(m-1)*(m+4),3*p*(p+5))==ratio_upper
            assert relative_upper<=R(16,p*(p+5))
            cases.append({'p':p,'q':q,'f':f,'m':m,'actual_degree_cost_bound':str(actual_degree_bound),
                          'closed_denominator_lower_bound':str(closed_bound),'ratio_to_base_lightness_upper':str(relative_upper)})
    return cases

if __name__=='__main__':
    result={'scope':'Finite exact-rational graph experiments only; no compiler/kernel/retrieval/cache invocation',
       'two_block_cases':[two_blocks(4,2,1),two_blocks(5,3,1)],'weighted_blowup_quantile_cases':quantile_obstruction(),
       'proved_vs_tested':'Arbitrary-parameter handwritten arguments are in REPORT.md and await independent review; finite tests are supporting experiments only.',
       'general_Theorem34_repair':'OPEN; no acceptance or completion claim'}
    (HERE/'experiment-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'two_block_cases':result['two_block_cases'],'quantile_cases':len(result['weighted_blowup_quantile_cases']),'status':'all finite assertions passed'},indent=2))
