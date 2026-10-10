"""Independent finite checks of the explicit guard-collision family.
These are diagnostics, not Lean proofs or a general cubic-progress theorem.
"""
import json

def check(m):
    assert m>=3
    names=['s']+[('a',i) for i in range(1,2*m+1)]+[('w',i) for i in range(1,3*m)]+['z','b']+[('a',i) for i in range(2*m+1,3*m+1)]
    ix={x:i for i,x in enumerate(names)};N=len(names)
    edges=set()
    for path in [['s']+[('a',i) for i in range(1,3*m+1)],['s']+[('w',i) for i in range(1,3*m)]+['z','b']]:
        edges.update((ix[a],ix[b]) for a,b in zip(path,path[1:]))
    edges.update((ix[('a',i)],ix['b']) for i in range(1,m+1))
    edges.update((ix['b'],ix[('a',j)]) for j in range(2*m+1,3*m+1))
    assert all(a<b for a,b in edges)
    adj=[[] for _ in names]
    for a,b in edges:adj[a].append(b)
    reach=[0]*N
    for a in reversed(range(N)):
        reach[a]=1<<a
        for b in adj[a]:reach[a]|=reach[b]
    chains=[[i] for i,v in enumerate(names) if v not in ['z','b']]+[[ix['z'],ix['b']]]
    label={v:c for c,vs in enumerate(chains) for v in vs}
    selector=[]
    for s in range(N):selector.append({c:next((v for v in vs if reach[s]>>v&1),None) for c,vs in enumerate(chains)})
    def allowed(s,a,b):return label[a]==label[b] or selector[s][label[b]]==b
    def distances(s,extra=None):
        ds=[10**9]*N;ways=[0]*N;ds[s]=1;ways[s]=1
        for a in range(s,N):
            if ds[a]>=10**9:continue
            for b in adj[a]+([extra[1]] if extra and a==extra[0] else []):
                if not allowed(s,a,b):continue
                val=ds[a]+(label[a]!=label[b])
                if val<ds[b]:ds[b]=val;ways[b]=ways[a]
                elif val==ds[b]:ways[b]+=ways[a]
        return ds,ways
    edge=(ix[('w',m)],ix[('w',2*m)])
    assert reach[edge[0]]>>edge[1]&1
    all_d=[distances(s) for s in range(N)]
    L=3*m+1;raw_drop=0;maximum=0
    for s in range(N):
        ds,_=all_d[s];dn,_=distances(s,edge)
        for t in selector[s].values():
            if t is not None:
                assert ds[t]<10**9 and dn[t]<=ds[t]
                maximum=max(maximum,ds[t]);raw_drop+=ds[t]-dn[t]
    assert maximum==L
    s=ix['s'];z=ix['z'];b=ix['b']
    for j in range(1,3*m+1):
        a=ix[('a',j)];assert all_d[s][0][a]==j+1 and all_d[s][1][a]==1
    assert all_d[s][0][z]==L
    collisions=0
    for i in range(1,m+1):
        a=ix[('a',i)];assert not(reach[a]>>z&1)
        for j in range(2*m+1,3*m+1):
            t=ix[('a',j)];assert all_d[a][0][t]==3 and all_d[a][1][t]==1
            assert all_d[s][0][t]>all_d[s][0][a]+3
            assert allowed(a,a,b) and allowed(a,b,t)
            assert not allowed(s,a,b) and allowed(s,b,t)
            assert selector[s][label[b]]==z
            collisions+=1
    assert collisions==m*m
    for i in range(1,m+1):
        a=ix[('w',i)];dn,_=distances(a,edge)
        for j in range(2*m,3*m):
            t=ix[('w',j)];assert all_d[a][0][t]==j-i+1
            assert all_d[a][0][t]-dn[t]==m-1
    n=(6*m+1)**2
    assert N==6*m+2 and len(chains)==6*m+1 and L**3>n
    assert raw_drop>=m*m*(m-1)
    return dict(m=m,core_vertices=N,chains=len(chains),padded_vertices=n,L=L,active=True,strict_failed_pairs=collisions,distinct_constructed_guards=1,raw_drop=raw_drop,rectangle_lower=m*m*(m-1))

if __name__=='__main__':
    print(json.dumps({'status':'PASS_FINITE_GUARD_COLLISION_DIAGNOSTICS','scope':'Explicit supplied-cover empty-H family only; not a general cubic-progress theorem.','cases':[check(m) for m in [3,4,8,16,32,64]]},indent=2))
