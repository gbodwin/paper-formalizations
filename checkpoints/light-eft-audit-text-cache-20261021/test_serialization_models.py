"""Pure differential serialization models; no Lean, timing or receipt acceptance."""
from dataclasses import dataclass
from pathlib import Path
import contextlib,fcntl,hashlib,json,os,random,resource,subprocess,time,unittest
from unittest.mock import patch

@dataclass(frozen=True)
class NameKey:
    parts: tuple

class CollidingKey(NameKey):
    def __hash__(self):return 0

class Formatter:
    """An arbitrary pure formatter oracle, not a Lean Name pretty-printer model."""
    def __init__(self,views=None):self.views=views or {};self.calls=[]
    def __call__(self,name):
        self.calls.append(name)
        return self.views.get(name,json.dumps(name.parts,ensure_ascii=False,separators=(',',':')))

class Memo:
    def __init__(self,formatter):self.cache={};self.formatter=formatter
    def __call__(self,name):
        if name not in self.cache:self.cache[name]=self.formatter(name)
        return self.cache[name]
    def names(self,names):return ','.join(self(n) for n in names)

def direct_names(formatter,names):return ','.join(map(formatter,names))

def tables(inventory,dependencies,formatter,cached):
    render=Memo(formatter) if cached else formatter
    names=render.names if cached else lambda ns:direct_names(render,ns)
    inv='owner\tname\tkind\tunsafe\tpartial\n'
    for owner,name,kind,unsafe,partial in inventory:
        inv+=f'{render(owner)}\t{render(name)}\t{kind}\t{str(unsafe).lower()}\t{str(partial).lower()}\n'
    dep='name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n'
    for name,owner,kind,types,body,unsafe,partial in dependencies:
        dep+=f'{render(name)}\t{render(owner)}\t{kind}\t{names(types)}\t{names(body)}\t{str(unsafe).lower()}\t{str(partial).lower()}\n'
    return inv.encode(),dep.encode(),render.cache if cached else None

def graph_rows(graph,roots,allowed,observe=None):
    """Small supplied-graph traversal model; actual Lean Expr traversal is unchanged."""
    inventory=[];rows=[];issues=[];visited=set();todo=list(roots);axioms=set();opaque=0
    for n in roots:
        c=graph[n];inventory.append((c['owner'],n,c['kind'],c['unsafe'],c['partial']))
        if c['unsafe']:issues.append(('root unsafe',n))
        if c['partial']:issues.append(('root partial',n))
        if c['kind']=='axiom':issues.append(('root axiom',n))
    while todo:
        n=todo.pop(0)
        if n in visited:continue
        visited.add(n)
        if n not in graph:raise ValueError(('Unresolved recursive dependency',n))
        c=graph[n]
        if c['unsafe']:issues.append(('recursive unsafe',n))
        if c['partial']:issues.append(('recursive partial',n))
        if c['kind']=='axiom':
            if n not in allowed:issues.append(('recursive disallowed axiom',n))
            axioms.add(n)
        if c['kind']=='opaque':opaque+=1
        rows.append((n,c['owner'],c['kind'],c['types'],c['body'],c['unsafe'],c['partial']))
        if observe is not None:observe(rows[-1])
        todo=list(c['types'])+list(c['body'])+todo
    return inventory,rows,(visited,issues,axioms,opaque)

def forbidden(*a,**k):raise AssertionError('Native/lease/resource action forbidden in source-only models')
def key(n):return NameKey((('str',str(n)),))

class Models(unittest.TestCase):
    def setUp(self):
        stack=contextlib.ExitStack();self.addCleanup(stack.close)
        for owner,name in [(subprocess,'Popen'),(fcntl,'flock'),(resource,'setrlimit'),(os,'fork'),(os,'killpg'),(os,'waitid'),(os,'wait4'),(os,'waitpid'),(time,'sleep')]:
            stack.enter_context(patch.object(owner,name,side_effect=forbidden))
    def same(self,inv,rows,views=None):
        a,b=Formatter(views),Formatter(views)
        old=tables(inv,rows,a,False);new=tables(inv,rows,b,True)
        self.assertEqual(old[:2],new[:2])
        self.assertEqual(b.calls,list(dict.fromkeys(a.calls)))
        for name,text in new[2].items():self.assertEqual(text,Formatter(views)(name))
        return a,b,old,new
    def test_empty_singleton_and_all_constant_kinds(self):
        self.same([],[])
        for kind in ['axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor']:
            self.same([(key('M'),key('n'),kind,False,False)],[(key('n'),key('M'),kind,[],[],False,False)])
    def test_unicode_numeric_empty_private_and_display_aliases(self):
        ns=[NameKey(()),NameKey((('str',''),)),NameKey((('num',0),)),NameKey((('str','0'),)),NameKey((('str','_private'),('num',10**80),('str','helper'))),key('日本語'),key('é'),key('é'),key('a\tb\nc')]
        views={n:'alias' if i in [2,3] else s for i,(n,s) in enumerate(zip(ns,['anonymous','','alias','alias','_private.large.helper','日本語','é','é','a\tb\nc']))}
        self.same([],[(n,key('M'),'theorem',ns,ns,False,False) for n in ns],views)
    def test_duplicate_lists_and_order_are_not_normalized(self):
        ns=[key('b'),key('a'),key('b')]
        _,_,old,_=self.same([],[(key('n'),key('M'),'theorem',ns,ns,False,False)],{n:n.parts[0][1] for n in ns+[key('n'),key('M')]})
        self.assertIn(b'b,a,b\tb,a,b',old[1])
    def test_hash_collisions_use_complete_keys(self):
        ns=[CollidingKey((('str',str(i)),)) for i in range(64)]
        self.same([],[(n,ns[0],'definition',ns,ns,False,False) for n in ns])
    def test_graph_cycles_violations_axioms_and_opaque_counts(self):
        ns=[key(i) for i in range(8)];kinds=['axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor']
        graph={n:dict(owner=key('M'),kind=kinds[i],types=[ns[(i+1)%8],n],body=[ns[(i+2)%8]],unsafe=i==1,partial=i==2) for i,n in enumerate(ns)}
        inv,rows,state=graph_rows(graph,[ns[1],ns[0]],set())
        self.same(inv,rows);self.assertEqual(len(state[0]),8);self.assertEqual(state[2],{ns[0]});self.assertEqual(state[3],1);self.assertTrue(state[1])
    def test_unresolved_dependency_still_rejects(self):
        n=key('n');graph={n:dict(owner=key('M'),kind='theorem',types=[key('missing')],body=[],unsafe=False,partial=False)}
        prefixes=[]
        for cached in [False,True]:
            prefix=[]
            def observe(row):prefix.append(tables([], [row], Formatter(), cached)[1])
            with self.assertRaises(ValueError) as e:graph_rows(graph,[n],set(),observe)
            self.assertEqual(e.exception.args[0],('Unresolved recursive dependency',key('missing')))
            self.assertEqual(len(prefix),1);prefixes.append(prefix)
        self.assertEqual(prefixes[0],prefixes[1])
    def test_seeded_supplied_graph_differentials(self):
        rng=random.Random(51539)
        for _ in range(100):
            ns=[key(i) for i in range(24)]
            graph={n:dict(owner=key('M'+str(i%3)),kind=rng.choice(['definition','theorem','opaque','axiom']),types=rng.choices(ns,k=rng.randrange(5)),body=rng.choices(ns,k=rng.randrange(5)),unsafe=rng.randrange(20)==0,partial=rng.randrange(20)==0) for i,n in enumerate(ns)}
            inv,rows,_=graph_rows(graph,ns[:3],{ns[0]});self.same(inv,rows)
    def test_structural_formatter_call_reduction_and_fresh_cache(self):
        ns=[key(i) for i in range(4096)];owners=[key('M'+str(i)) for i in range(8)]
        rows=[(n,owners[i%8],'theorem',[ns[(i+1)%len(ns)],ns[(i+2)%len(ns)],ns[0]], [ns[0],n,ns[(i+1)%len(ns)]],False,False) for i,n in enumerate(ns)]
        a,b,old,new=self.same([(owners[0],ns[0],'theorem',False,False)],rows)
        self.assertEqual(len(b.calls),4104);self.assertEqual(len(a.calls),32770)
        self.same([],rows[:1])
        print(json.dumps(dict(model='synthetic4096rows; not a Lean timing',reference_formatter_calls=len(a.calls),memoized_formatter_calls=len(b.calls),distinct_full_name_keys=len(new[2]),same_utf8_bytes=True,recursive_table_sha256=hashlib.sha256(old[1]).hexdigest(),native_execution=False)))

if __name__=='__main__':unittest.main(verbosity=2)
