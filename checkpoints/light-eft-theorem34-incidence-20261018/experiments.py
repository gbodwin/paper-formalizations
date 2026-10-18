"""Finite projective-incidence experiments. No Lean, network or subprocess API."""
from pathlib import Path
from fractions import Fraction as R
from itertools import combinations
from math import isqrt
import hashlib,heapq,json

A=Path(__file__).resolve().parent
def edge(u,v):return (min(u,v),max(u,v))
def distances(n,weights,F,source):
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

def geometry(p,q):
    assert p>=q and all(p%i for i in range(2,isqrt(p)+1))
    reps=sorted([(1,x,y) for x in range(p) for y in range(p)]+[(0,1,x) for x in range(p)]+[(0,0,1)])
    m=len(reps);n=2*m;assert m==p*p+p+1
    inc=[{j for j,z in enumerate(reps) if sum(x*y for x,y in zip(v,z))%p==0} for v in reps]
    byline=[{u for u in range(m) if j in inc[u]} for j in range(m)]
    assert all(len(x)==p+1 for x in inc+byline)
    edges={edge(u,m+j) for u in range(m) for j in inc[u]}
    pair_count=0;sample=None
    for u,v in combinations(range(m),2):
        shared=inc[u]&inc[v];assert len(shared)==1;l=next(iter(shared))
        paths=[[u,m+l,v]]
        for i,j in zip(sorted(inc[u]-{l}),sorted(inc[v]-{l})):
            z=byline[i]&byline[j];assert len(z)==1;z=next(iter(z));paths.append([u,m+i,z,m+j,v])
        used=set()
        for path in paths:
            es={edge(x,y) for x,y in zip(path,path[1:])}
            assert len(set(path))==len(path) and es<=edges and not (es&used);used|=es
        assert len(paths)==p+1;pair_count+=1
        if sample is None:sample=paths
    residual=set(edges);forests=[];C=set()
    for _ in range(q+1):
        parent=list(range(n))
        def find(u):
            while parent[u]!=u:parent[u]=parent[parent[u]];u=parent[u]
            return u
        forest=[]
        for e in sorted(residual):
            x,y=map(find,e)
            if x!=y:parent[x]=y;forest.append(e)
        assert len(forest)<=n-1
        # Maximality: every remaining edge's endpoints are forest-connected.
        assert all(find(u)==find(v) for u,v in residual)
        residual-=set(forest);C|=set(forest);forests.append(forest)
    assert len(C)<=min(len(edges),(q+1)*(n-1)) and len(C)>=m*(q+1)
    cut_tests=0;minimum=None
    if p==2:
        for mask in range(1,(1<<n)-1):
            count=sum(((mask>>u)&1)!=((mask>>v)&1) for u,v in C)
            assert count>=q+1;minimum=count if minimum is None else min(minimum,count);cut_tests+=1
    info={'p':p,'q':q,'m_points':m,'m_line_helpers':m,'n_total':n,'incidence_edges':len(edges),
       'projective_representatives':reps,'preserver_C_edges':sorted(C),'residual_forests':forests,
       'preserver_edge_count':len(C),'cost_coefficient_lower':m*(q+1),'cost_coefficient_upper':(q+1)*(n-1),
       'point_pair_disjoint_path_families_checked':pair_count,'sample_paths':sample,
       'exhaustive_nontrivial_cut_tests':cut_tests,'minimum_cut_if_exhaustive':minimum,
       'cut_scope':'exhaustive every nontrivial cut' if p==2 else 'forest maximality and path disjointness checked; no exhaustive cut enumeration'}
    return info,inc,edges,C

def weighted_case(info,inc,edges,C,f,a):
    p=info['p'];q=info['q'];m=info['m_points'];n=2*m;split=m//2
    heavy={edge(u,v):R(1) for u in range(split) for v in range(split,m)}
    K={e:a for e in edges};G=K|heavy
    D_lower=a*m*(q+1);cost_C=a*len(C)
    assert D_lower<=cost_C<=a*(q+1)*(n-1)
    witness_count=0;small_count=0;sample=None
    for e in heavy:
        u,v=e;l=next(iter(inc[u]&inc[v]));F={edge(u,m+l)}
        alt=distances(n,{x:w for x,w in G.items() if x!=e},F,u)[v]
        g=distances(n,G,F,u)[v];k=distances(n,K,F,u)[v]
        assert k==4*a
        if a>R(1,2):
            assert g==1 and alt==1+2*a>2;witness_count+=1
        else:
            assert k<=2 and k<=2*g;small_count+=1
        if sample is None:sample={'heavy_edge':e,'fault':sorted(F),'full_graph_alternative_distance':str(alt),'incidence_only_alternative_distance':str(k),'input_distance':str(g)}
    comparisons=0
    if p==2 and a<=R(1,2):
        faults=[set()]+[{e} for e in G]
        for F in faults:
            for u in range(n):
                dg=distances(n,G,F,u);dk=distances(n,K,F,u)
                for v in range(n):
                    assert dg[v] is not None and dk[v] is not None and dk[v]<=2*dg[v]
            comparisons+=1
    return {'p':p,'q':q,'f':f,'a':str(a),'n_with_all_helpers':n,'heavy_edges':len(heavy),
       'certificate_C_cost':str(cost_C),'genuine_denominator_lower_bound':str(D_lower),
       'all_heavy_forcing_witnesses_checked':witness_count,'targeted_nonforcing_fault_checks':small_count,
       'all_pairs_fault_sets_checked':comparisons,
       'all_pairs_scope':'every full-input fault set of size <=1' if comparisons else 'not enumerated; only specified targeted fault sets',
       'sample':sample}

if __name__=='__main__':
    # PRECHECK.md was written first, before any graph experiment in this pass.
    precheck_hash=hashlib.sha256((A/'PRECHECK.md').read_bytes()).hexdigest()
    shapes=[];cases=[]
    for p,q,f in [(2,2,1),(3,2,1),(5,4,2),(7,2,1)]:
        info,inc,edges,C=geometry(p,q);shapes.append(info)
        if p==7:continue # Geometry/cost-only larger case, no distance experiments.
        for a in [R(1,4*(f+1)**2),R(1,4),R(1,2),R(3,4),R(1)]:cases.append(weighted_case(info,inc,edges,C,f,a))
    summary={'geometries':len(shapes),'weighted_cases':len(cases),
       'point_pair_path_families':sum(s['point_pair_disjoint_path_families_checked'] for s in shapes),
       'exhaustive_cut_tests':sum(s['exhaustive_nontrivial_cut_tests'] for s in shapes),
       'full_graph_forcing_witnesses':sum(c['all_heavy_forcing_witnesses_checked'] for c in cases),
       'targeted_nonforcing_fault_checks':sum(c['targeted_nonforcing_fault_checks'] for c in cases),
       'all_pairs_fault_sets':sum(c['all_pairs_fault_sets_checked'] for c in cases)}
    result={'scope':'Finite exact-rational experiments, not a Lean proof','pre_experiment_precheck_sha256':precheck_hash,
       'geometries':shapes,'weighted_cases':cases,'summary':summary,
       'status':'all finite assertions passed; full stretch2 target remains OPEN'}
    (A/'experiment-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(summary,indent=2))
