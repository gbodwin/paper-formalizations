"""Finite diagnostics of arXiv:2511.20111v2, not Lean proof or theorem refutation."""
from fractions import Fraction
from random import Random

def warmup():
    n, beta = 7, 4
    ds = [t-s for s in range(n) for t in range(s+1,n)]
    phi = sum(d for d in ds if 2*d > beta)
    p = sum(d > beta for d in ds)
    avg = Fraction(phi,p)
    assert (phi,p,max(ds)) == (40,3,6)
    assert max(ds) < avg
    print('Section 2.2 literal averaging counterexample:', {'graph':'directed path 0->1->...->6','beta':beta,'phi':phi,'p':p,'phi/p':str(avg),'max_hopdistance':max(ds)})

def reach(n, es):
    r=[[i==j for j in range(n)] for i in range(n)]
    for u,v in es:r[u][v]=True
    for k in range(n):
        for i in range(n):
            for j in range(n):r[i][j] |= r[i][k] and r[k][j]
    return r

def check(n,es,cs):
    r=reach(n,es)
    for c in cs:
        es |= {(u,v) for i,u in enumerate(c) for v in c[i+1:]}
    adj=[[v for v in range(n) if (u,v) in es] for u in range(n)]
    col={v:i for i,c in enumerate(cs) for v in c}
    earliest={(s,i):next((v for v in c if r[s][v]),None) for s in range(n) for i,c in enumerate(cs)}
    pairs={(s,v) for (s,i),v in earliest.items() if v is not None}
    def valid(p):
        for i,c in enumerate(cs):
            inds=[j for j,v in enumerate(p) if v in c]
            if inds and (inds != list(range(inds[0],inds[-1]+1)) or p[inds[0]]!=earliest[p[0],i]):return False
        return True
    def cost(p):return len({col[v] for v in p if v in col})
    allp={}
    for s in range(n):
        stack=[(s,)]
        while stack:
            p=stack.pop(); allp.setdefault((s,p[-1]),[]).append(p)
            stack.extend(p+(v,) for v in adj[p[-1]])
    vp={key:[p for p in ps if valid(p)] for key,ps in allp.items()}
    mins={key:min(map(cost,ps)) for key,ps in vp.items() if ps}
    for key in pairs:
        for p in vp.get(key,[]):
            if cost(p)!=mins[key]:continue
            for i in range(len(p)):
                for j in range(i+1,len(p)):
                    q=p[i:j+1]; qkey=(q[0],q[-1])
                    if qkey in pairs and cost(q)>mins[qkey]:
                        return {'n':n,'edges':sorted(es),'chains':cs,'pair':key,'minimal_valid_path':p,'cost':cost(p),'subpath':q,'subpath_cost':cost(q),'shorter_valid_subpath':next(z for z in vp[qkey] if cost(z)==mins[qkey]),'minimum_subpath_cost':mins[qkey]}
    return None

if __name__=='__main__':
    warmup()
    rng=Random(251120111)
    for trial in range(6000):
        n=10
        es={(u,v) for u in range(n) for v in range(u+1,n) if rng.random()<.20}
        r=reach(n,es)
        cs=[]; remaining=list(range(n)); rng.shuffle(remaining)
        while remaining:
            c=[remaining.pop()]
            for v in remaining[:]:
                if all(r[min(v,w)][max(v,w)] for w in c):c.append(v);remaining.remove(v)
            cs.append(sorted(c))
        result=check(n,es.copy(),cs)
        if result:
            print('Section 5.7 literal hereditary optimality counterexample:',result);break
    else:print('No hereditary-optimality counterexample in 6000 random DAG instances (not a proof).')

    # Deterministic diagnostic: validity is inherited but optimality need not be.
    es={(0,1),(1,2),(2,3),(3,9),(0,4),(4,5),(5,6),(6,7),(7,8),(8,9),(1,8)}
    cs=[[0],[1],[2],[3],[4],[5],[6],[7,8],[9]]
    result=check(10,es,cs)
    assert result and result['cost']==5 and result['subpath_cost']==4 and result['minimum_subpath_cost']==3
    assert len(cs)**3 <= 8*10**2  # 9 <= 2 * 10^(2/3)
    print('Deterministic Lemma 5.7 intermediate-claim diagnostic:',result)
