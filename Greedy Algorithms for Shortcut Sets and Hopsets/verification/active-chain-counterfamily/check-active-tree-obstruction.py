"""Independent finite checks of the symbolic near-maximum repair obstruction.
Only the covered core is materialized. Isolated padding affects n, not distances.
No raw-potential best-edge bound or main-theorem counterexample is asserted.
"""
from itertools import product
import json

def check(h,k):
    nodes=[''.join(p) for d in range(h+1) for p in product('01',repeat=d)]
    names=[('r',)]
    for height in range(h+1):
        level=[u for u in nodes if h-len(u)==height]
        names += [v for u in level for v in [('x',u),('y',u)]]
        if height<h:
            names += [('z',u,j) for u in level for j in range(1,k+1)]
    ix={v:i for i,v in enumerate(names)}
    edges={(ix[('x',u)],ix[('y',u)]) for u in nodes}
    for u in nodes:
        if len(u)==h:edges.add((0,ix[('x',u)]))
        if u:
            path=[('y',u)]+[('z',u,j) for j in range(1,k+1)]+[('x',u[:-1])]
            edges.update((ix[a],ix[b]) for a,b in zip(path,path[1:]))
        for d in range(1,len(u)):
            a=u[:d];b=a[:-1]+str(1-int(a[-1]))
            edges.add((ix[('y',u)],ix[('y',b)]))
    N=len(names);adj=[[] for _ in names]
    for a,b in edges:
        assert a<b,(names[a],names[b]);adj[a].append(b)
    reach=[0]*N
    for a in reversed(range(N)):
        reach[a]=1<<a
        for b in adj[a]:reach[a]|=reach[b]
    chains=[[0]]+[[ix[('x',u)],ix[('y',u)]] for u in nodes]
    chains += [[i] for i,v in enumerate(names) if v[0]=='z']
    M=len(chains);T=len(nodes)
    assert M==1+T+(T-1)*k and N==M+T and M*M>=N
    color=[None]*N
    for c,ch in enumerate(chains):
        for v in ch:color[v]=c
    L=h*(k+1)+2;global_max=0;other_max=0;tree_max=0;count=0
    for s,v in enumerate(names):
        if v[0] in ('x','y'):
            u=v[1];A={u[:d] for d in range(len(u)+1)}
            B={u[:d-1]+str(1-int(u[d-1])) for d in range(1,len(u))}
            want={('y',u)}|({('x',u)} if v[0]=='x' else set())
            want|={w for a in A-{u} for w in [('x',a),('y',a)]}
            want|={('y',b) for b in B}
            want|={('z',w,j) for w in A|B if w for j in range(1,k+1)}
            expected=sum(1<<ix[w] for w in want)
            assert reach[s]==expected,(h,k,v,'selector reachability')
        first=[next((a for a in ch if reach[s]>>a&1),None) for ch in chains]
        ds=[N+1]*N;ds[s]=1
        for a in range(s,N):
            if ds[a]>N:continue
            for b in adj[a]:
                if color[a]!=color[b] and first[color[b]]!=b:continue
                ds[b]=min(ds[b],ds[a]+(color[a]!=color[b]))
        vals=[ds[a] for a in first if a is not None]
        assert all(d<=N for d in vals)
        m=max(vals);global_max=max(global_max,m);count+=len(vals)
        if s:
            other_max=max(other_max,m);assert m<=3*k+3,(h,k,v,m)
            if v[0] in ('x','y'):
                tree_max=max(tree_max,m);assert m<=2*k+3,(h,k,v,m)
        else:
            for u in nodes:assert ds[ix[('x',u)]]==(h-len(u))*(k+1)+2
            for u in nodes:
                if u:
                    for j in range(1,k+1):
                        assert ds[ix[('z',u,j)]]==(h-len(u))*(k+1)+j+2
    assert global_max==L
    n=M*M
    assert M**3<=8*n*n and 1<=n
    return dict(h=h,k=k,core_vertices=N,chains=M,padded_vertices=n,L=L,
        active=L**3>n,all_source_max=global_max,nonroot_max=other_max,
        tree_source_max=tree_max,important_pairs=count)

if __name__=='__main__':
    results=[check(h,k) for h in (2,3,4) for k in (1,2,3)]
    for h,k in [(4,16),(5,32)]:
        r=check(h,k);assert r['active'];results.append(r)
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS','scope':'Independent all-source checks; symbolic quantified proof separate; no cubic-drop assertion.','results':results},indent=2))
