from itertools import combinations,permutations
from fractions import Fraction
import json
vertices=range(5)
edges={tuple(e):Fraction(1) for e in combinations(range(4),2)}
edges[(0,4)]=Fraction(10)
def connected(es):
 seen={0}
 while True:
  new=seen|{v for u,v in es if u in seen}|{u for u,v in es if v in seen}
  if new==seen:return len(seen)==5
  seen=new
trees=[t for t in combinations(edges,4) if connected(t)]
weights=[sum(edges[e] for e in t) for t in trees]
metric=[]
for (u,v),w in edges.items():
 costs=[]
 other=[x for x in vertices if x not in [u,v]]
 for n in range(len(other)+1):
  for perm in permutations(other,n):
   path=(u,)+perm+(v,); ep=[tuple(sorted(e)) for e in zip(path,path[1:])]
   if all(e in edges for e in ep):costs.append(sum(edges[e] for e in ep))
 metric.append({'edge':[u,v],'weight':str(w),'shortest':str(min(costs)),'unique_shortest':costs.count(min(costs))==1})
assert all(x['unique_shortest'] and x['weight']==x['shortest'] for x in metric)
sparsity=Fraction(len(edges),5);lightness=sum(edges.values())/min(weights)
assert lightness<sparsity
print(json.dumps({'kind':'exhaustive exact-rational finite graph calculation; not a Lean theorem','vertices':5,'edges':[{'ends':e,'weight':str(w)} for e,w in edges.items()],'spanning_trees':len(trees),'minimum_tree_weight':str(min(weights)),'total_weight':str(sum(edges.values())),'sparsity':str(sparsity),'lightness':str(lightness),'unique_metric_edges':metric,'claim_lightness_ge_sparsity':False},indent=2))
