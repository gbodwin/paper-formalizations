from itertools import combinations
import json
n=10
E={(0,1),(1,3),(3,5),(5,7),(7,9),(0,2),(2,4),(4,6),(6,8),(8,9),(1,8),(2,7)}
chains=[(0,),(1,),(2,),(3,),(4,),(5,7),(6,8),(9,)]
col={v:i for i,c in enumerate(chains) for v in c}
adj={u:sorted(v for a,v in E if a==u) for u in range(n)}
def paths(s,t):
 if s==t:
  yield (s,);return
 for v in adj[s]:
  if v<=t:
   for p in paths(v,t):yield(s,)+p
all_paths={(s,t):list(paths(s,t)) for s in range(n) for t in range(s,n)}
reachable=lambda s,t:bool(all_paths.get((s,t),[]))
first={(s,i):next((v for v in c if reachable(s,v)),None)for s in range(n)for i,c in enumerate(chains)}
S={(s,v)for(s,i),v in first.items()if v is not None}
def valid(p):
 for i,c in enumerate(chains):
  pos=[k for k,v in enumerate(p)if v in c]
  if pos and (p[pos[0]]!=first[p[0],i]or pos!=list(range(pos[0],pos[-1]+1))):return False
 return True
def cost(p):return len({col[v]for v in p})
validpaths={st:[p for p in ps if valid(p)]for st,ps in all_paths.items()}
d={st:min(map(cost,ps))for st,ps in validpaths.items()if ps}
assert all(st in d for st in S)
L=max(d[st]for st in S)
maxpairs=sorted(st for st in S if d[st]==L)
rows=[]
for st in maxpairs:
 for p in validpaths[st]:
  if cost(p)!=L:continue
  failures=[]
  for i in range(len(p)):
   for j in range(i,len(p)):
    pair=(p[i],p[j]);sub=p[i:j+1]
    if pair in S and cost(sub)>d[pair]:
     failures.append({'pair':pair,'subpath':sub,'subcost':cost(sub),'distance':d[pair],'witness':next(q for q in validpaths[pair]if cost(q)==d[pair])})
  assert failures
  rows.append({'pair':st,'path':p,'cost':cost(p),'failures':failures})
assert len(chains)**3<=8*n*n
assert set(col)==set(range(n))
assert all(reachable(u,v) for c in chains for u,v in combinations(c,2))
assert all((u,v)in E for c in chains for u,v in combinations(c,2))
assert L==5 and maxpairs==[(0,9)] and len(rows)==2
print(json.dumps({'n':n,'edges':sorted(E),'chains':chains,'S_size':len(S),'L':L,'maxpairs':maxpairs,'max_shortest_paths':rows,'maximum_distance_by_source':{s:max(d[st]for st in S if st[0]==s)for s in range(n)},'important_distances':[[*st,d[st]]for st in sorted(S)],'cover_check':'All vertices covered, 8^3 <= 8*10^2; chain segments are already 1-hop.'},indent=2))
