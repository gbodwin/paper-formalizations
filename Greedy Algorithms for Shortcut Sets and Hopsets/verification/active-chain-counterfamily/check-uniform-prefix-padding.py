"""Finite diagnostics of distance/potential-preserving uniform chain padding.
Not a Lean proof, and not a counterexample to cubic progress.
"""
import json,random,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from chain_potential_model import analyze
from check_source_examples import reach

def pad(n,edges,chains,r):
    assert all(len(c)<=r for c in chains)
    nadd=sum(r-len(c) for c in chains)
    out={(a+nadd,b+nadd) for a,b in edges};new=[];cursor=0
    for c in chains:
        ps=list(range(cursor,cursor+r-len(c)));cursor+=len(ps)
        cc=ps+[v+nadd for v in c];new.append(cc)
        out.update(zip(cc,cc[1:]))
        out.update((p,v+nadd) for p in ps for v in range(n))
    return n+nadd,out,new,nadd

def check(n,edges,chains,r):
    assert sorted(v for c in chains for v in c)==list(range(n))
    # Require the input's consecutive chain arcs to be present.
    assert all((a,b) in edges for c in chains for a,b in zip(c,c[1:]))
    N,E,C,A=pad(n,edges,chains,r)
    old=analyze(n,edges,chains);new=analyze(N,E,C)
    assert [(s-A,t-A,d) for s,t,d in new['records'] if s>=A]==old['records']
    I=len(chains);assert N==I*r
    assert all(d==(1 if any(s in c and t in c for c in C) else 2) for s,t,d in new['records'] if s<A)
    assert new['phi']==old['phi']+A*(2*I-1)
    closure=reach(n,edges)
    for u in range(n):
        for v in range(u+1,n):
            if closure[u][v]:
                old_after=analyze(n,edges|{(u,v)},chains)
                new_after=analyze(N,E|{(u+A,v+A)},C)
                assert old['phi']-old_after['phi']==new['phi']-new_after['phi']
    padded_closure=reach(N,E)
    for u in range(A):
        for v in range(u+1,N):
            if padded_closure[u][v]:
                assert analyze(N,E|{(u,v)},C)['phi']==new['phi']
    og=analyze(n,edges,chains,True);ng=analyze(N,E,C,True)
    assert og['best_drop']==ng['best_drop']
    assert ng['L']==max(og['L'],2 if A and I>1 else 1)
    # Check the same preservation again at a legal nonempty shortcut state.
    closure=reach(n,edges)
    choices=[(u,v) for u in range(n) for v in range(u+1,n) if closure[u][v] and (u,v) not in edges]
    if choices:
        h=choices[len(choices)//2];after=analyze(n,edges|{h},chains)
        padded_after=analyze(N,E|{(h[0]+A,h[1]+A)},C)
        assert [(s-A,t-A,d) for s,t,d in padded_after['records'] if s>=A]==after['records']
        assert padded_after['phi']-after['phi']==A*(2*I-1)
        assert analyze(n,edges|{h},chains,True)['best_drop']==analyze(N,E|{(h[0]+A,h[1]+A)},C,True)['best_drop']
    return {'core_vertices':n,'chains':I,'uniform_size':r,'padded_vertices':N,
        'padded_sources':A,'old_maximum':og['L'],'old_best_drop':og['best_drop'],
        'padded_best_drop':ng['best_drop'],'constant_potential_offset':A*(2*I-1)}

rng=random.Random(731184)
checks=[]
# Exact asymmetric hereditary-obstruction instance.
es={(0,1),(1,2),(2,3),(3,9),(0,4),(4,5),(5,6),(6,7),(7,8),(8,9),(1,8)}
checks.append(check(10,es,[[0],[1],[2],[3],[4],[5],[6],[7,8],[9]],3))
for k in range(12):
    n=5+k%3;chains=[];v=0
    while v<n:
        size=2 if v+1<n and rng.random()<0.5 else 1
        chains.append(list(range(v,v+size)));v+=size
    es={(a,b) for a in range(n) for b in range(a+1,n) if rng.random()<0.3}
    es|={(a,b) for c in chains for a,b in zip(c,c[1:])}
    checks.append(check(n,es,chains,3))
out={'scope':'Independent finite diagnostics only; no Lean theorem and no cubic-progress counterexample',
    'assertions':['All original-source important distances unchanged','Each added-source row is at its absolute lower bound','Raw potential changes by the stated constant offset','Every old legal candidate has exactly its original drop, and every fresh-endpoint candidate has zero drop','An inherited nonempty legal shortcut state also preserves distances and offset'],
    'checks':checks}
Path(__file__).with_name('uniform-prefix-padding-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('Uniform padding diagnostics passed:',len(checks),'instances with exhaustive best-edge recomputation.')
