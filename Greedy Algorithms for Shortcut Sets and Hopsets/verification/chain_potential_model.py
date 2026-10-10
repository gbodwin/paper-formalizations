"""Finite DAG diagnostics for the normalized-distance definition in arXiv2511.20111v2.
No theorem verification is claimed. Vertices use a fixed topological order.
"""
from math import ceil
from check_source_examples import reach

def analyze(n, edges, chains, greedy=False):
    r=reach(n,edges)
    color={v:i for i,c in enumerate(chains) for v in c}
    earliest=[[next((v for v in c if r[s][v]),None) for c in chains] for s in range(n)]
    adj=[[v for u,v in sorted(edges) if u==s] for s in range(n)]
    inf=n+1
    def all_dist(extra=None):
        potential=0; largest=0; records=[]
        for s in range(n):
            ds=[inf]*n;ds[s]=int(s in color)
            for u in range(s,n):
                if ds[u]==inf:continue
                vs=adj[u]+([extra[1]] if extra is not None and extra[0]==u else [])
                for v in vs:
                    cv=color.get(v);cu=color.get(u)
                    if cv is not None and cu!=cv and earliest[s][cv]!=v:continue
                    cost=int(cv is not None and cu!=cv)
                    ds[v]=min(ds[v],ds[u]+cost)
            for v in earliest[s]:
                if v is not None:
                    assert ds[v]!=inf,(s,v)
                    potential+=ds[v];largest=max(largest,ds[v]);records.append((s,v,ds[v]))
        return potential,largest,records
    phi,L,records=all_dist()
    if not greedy:return {'phi':phi,'L':L,'records':records}
    best=(0,None)
    for u in range(n):
        for v in range(u+1,n):
            if r[u][v] and (u,v) not in edges:
                p,_,_=all_dist((u,v))
                if phi-p>best[0]:best=(phi-p,(u,v))
    return {'phi':phi,'L':L,'best_drop':best[0],'best_edge':best[1],'drop_over_L_cubed':best[0]/L**3}

if __name__=='__main__':
    es={(0,1),(1,2),(2,3),(3,9),(0,4),(4,5),(5,6),(6,7),(7,8),(8,9),(1,8)}
    cs=[[0],[1],[2],[3],[4],[5],[6],[7,8],[9]]
    a=analyze(10,es,cs)
    assert a['L']==5
    assert (0,9,5) in a['records'] and (1,9,3) in a['records']
    print('Exact example normalized potential:',analyze(10,es,cs,True))
    for length in [5,10,15,20]:
        # Two branches, with a source-dependent forbidden shortcut through one chain.
        target=2*length-1
        main=list(range(length-1))+[target]
        branch=[0]+list(range(length-1,2*length-1))+[target]
        es=set(zip(main,main[1:]))|set(zip(branch,branch[1:]))|{(1,target-1)}
        merged=[target-2,target-1]
        cs=[[v] for v in range(2*length) if v not in merged]+[merged]
        n=max(2*length,ceil((len(cs)/2)**1.5))
        assert len(cs)**3<=8*n*n
        a=analyze(n,es,cs,True)
        print('Scaled diagnostic',{'n':n,'chains':len(cs),**a})
