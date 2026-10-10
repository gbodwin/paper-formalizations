"""Finite verification supporting the separate all-m mathematical proof.

No external packages; no formalization files are changed. Dynamic programming
uses original earliest-entry selectors and counts chains, including source.
In this family (also after the tested edge) no path can leave and revisit a
chain, so chain-transition count equals distinct visited-chain count.
"""
from math import inf
import json


def instance(m):
    assert m >= 2
    vertices = ['r'] + [f'{arm}{i}' for i in range(1, m+1)
                          for arm in ('a', 'b')] + ['xA','xB','yA','yB','t']
    chains = [('r',)] + [(f'{arm}{i}',) for i in range(1,m+1)
                       for arm in ('a','b')] + [('xA','yA'),('xB','yB'),('t',)]
    edges = {('r','a1'), ('r','b1'), ('a1','yB'), ('b1','yA'),
             (f'a{m}','xA'), (f'b{m}','xB'), ('xA','yA'),
             ('xB','yB'), ('yA','t'), ('yB','t')}
    edges |= {(f'{arm}{i}', f'{arm}{i+1}')
              for arm in ('a','b') for i in range(1,m)}
    color = {v:c for c,ch in enumerate(chains) for v in ch}
    index = {v:i for i,v in enumerate(vertices)}
    assert all(index[u] < index[v] for u,v in edges)
    adj = {u:[v for v in vertices if (u,v) in edges] for u in vertices}
    reach = {}
    for s in reversed(vertices):
        reach[s] = {s}
        for v in adj[s]: reach[s] |= reach[v]
    first = {(s,c):next((v for v in ch if v in reach[s]), None)
             for s in vertices for c,ch in enumerate(chains)}
    important = {(s,v) for (s,c),v in first.items() if v is not None}
    return vertices, chains, edges, color, first, important


def distances(vertices,edges,color,first):
    adj={u:[] for u in vertices}
    for u,v in edges: adj[u].append(v)
    result={}
    for s in vertices:
        d={v:inf for v in vertices}; d[s]=1
        for u in vertices:
            if d[u] == inf: continue
            for v in adj[u]:
                if color[u] != color[v] and first[s,color[v]] != v: continue
                d[v]=min(d[v],d[u]+(color[u] != color[v]))
        result.update({(s,t):value for t,value in d.items() if value < inf})
    return result


def verify(m):
    V,C,E,col,first,S=instance(m)
    d=distances(V,E,col,first)
    L=max(d[pair] for pair in S)
    assert L==m+3
    assert {pair for pair in S if d[pair]==L}=={('r','t')}
    adj={u:[v for v in V if (u,v) in E] for u in V}
    def paths(u,t):
        if u==t:
            yield (u,); return
        for v in adj[u]:
            for rest in paths(v,t): yield (u,)+rest
    def valid(p):
        for c,ch in enumerate(C):
            pos=[i for i,v in enumerate(p) if col[v]==c]
            if pos and (p[pos[0]] != first[p[0],c] or
                        pos != list(range(pos[0],pos[-1]+1))): return False
        return True
    def cost(p): return len({col[v] for v in p})
    minima=[p for p in paths('r','t') if valid(p) and cost(p)==L]
    assert len(minima)==2
    for p in minima:
        q=p[1:]
        assert valid(q) and cost(q)==m+2 and d[q[0],q[-1]]==3
        assert cost(q)*2 >= L and (q[0],q[-1]) in S
    def hereditary(p):
        return all(cost(p[i:j+1])==d[p[i],p[j]]
                   for i in range(len(p)) for j in range(i,len(p)))
    for arm,tail in [('a','A'),('b','B')]:
        near=('r',)+tuple(f'{arm}{i}' for i in range(1,m+1))+(f'x{tail}',)
        shifted=tuple(f'{arm}{i}' for i in range(2,m+1))+(f'x{tail}',f'y{tail}','t')
        assert valid(near) and cost(near)==L-1 and hereditary(near)
        assert valid(shifted) and cost(shifted)==L-2 and hereditary(shifted)
    p=m//3; q=2*m//3
    lower=0; drop=None
    if p>=1 and q>p+1:
        edge=(f'a{p}',f'a{q}')
        assert edge not in E and edge in d
        new=distances(V,E|{edge},col,first)
        drop=sum(d[pair]-new[pair] for pair in S)
        lower=p*(m-q+1)*(q-p-1)
        assert drop>=lower
        assert all(new[pair]<=d[pair] for pair in S)
    return dict(m=m,n=len(V),chains=len(C),L=L,unique_maximum=['r','t'],
                maximum_minimizers=2,bad_subpath_cost=m+2,rebased_cost=3,
                bad_ratio=3/(m+2),hereditary_distances=[L-1,L-2],
                tested_edge_drop=drop,rectangle_drop_lower_bound=lower)

if __name__=='__main__':
    print(json.dumps({'checked':[verify(m) for m in [2,3,4,8,16,32,64,128]],
                      'note':'Finite checks support the separate symbolic proof; they are not that proof.'},indent=2))
