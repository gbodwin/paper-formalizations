"""Differential encoding/allocation/provenance models, not native Lean evidence."""
from dataclasses import dataclass,field
import itertools,unittest

@dataclass(frozen=True)
class Name:
    value:tuple
    source:str=field(default='environment',compare=False)

ANON=();S=lambda pre,text:('str',pre,text);N=lambda pre,number:('num',pre,number)
def varint(n):
    result=bytearray()
    while n>=128:result.append(n%128+128);n//=128
    result.append(n);return bytes(result)
def encode(v):
    if not v:return b'\0'
    tag,pre,value=v
    if tag=='num':return encode(pre)+b'\2'+varint(value)
    raw=value.encode('utf8');return encode(pre)+b'\1'+varint(len(raw))+raw
POOL=[ANON,S(ANON,''),S(ANON,'0'),N(ANON,0),S(ANON,'é'),S(ANON,'é'),
      S(S(ANON,'a'),'»'),S(ANON,'a.»'),N(S(ANON,'_private'),2**200),S(ANON,'a\tb\nc日本語')]
class Keys:
    def __init__(self,seeds):
        self.cache={};self.encodes=0
        for n in seeds:
            if n not in self.cache:self.cache[n]=self.direct(n)
    def direct(self,n):self.encodes+=1;return encode(n.value)
    def get(self,n):
        if n in self.cache:return self.cache[n]
        return self.direct(n)

def model(modules,cached):
    claims={};decls={};events=[];issues=[];encodes=0;counts=dict(raw=0,extra=0,repetitions=0,overlaps=0,actual=0,duplicates=0)
    for owner,(effective,parts) in enumerate(modules):
        keys=Keys([n for n,_ in effective] if cached else [])
        key=keys.get if cached else keys.direct
        for consts,extras in parts:
            for names,aux in [(consts,False),(extras,True)]:
                for n in names:
                    k=key(n);counts['extra' if aux else 'raw']+=1
                    if k not in claims:claims[k]=(owner,aux)
                    elif claims[k][0]==owner:counts['repetitions']+=1
                    else:
                        counts['overlaps']+=1;events.append(('claim',k.hex(),claims[k][0],owner,aux or claims[k][1]))
        for slot,(n,kind) in enumerate(effective):
            k=key(n);counts['actual']+=1
            if k in decls:
                counts['duplicates']+=1;prior=decls[k]
                compatible=kind==prior[2]=='theorem'
                events.append(('declaration',k.hex(),prior[0],owner,compatible))
                if not compatible:issues.append((k.hex(),prior[0],owner))
                else:decls[k]=(owner,slot,kind)
            else:decls[k]=(owner,slot,kind)
        encodes+=keys.encodes
    return (claims,decls,events,issues,counts),encodes

class Models(unittest.TestCase):
    def test_empty_hits_misses_and_distinct_name_components(self):
        env=[Name(x) for x in POOL];raw=[Name(x,'reader') for x in POOL]
        for seeds in [[],env,env+env,env[:3]]:
            keys=Keys(seeds)
            for n in raw:self.assertEqual(keys.get(n),encode(n.value))
            self.assertEqual(len(keys.cache),len(set(seeds)))
            self.assertEqual(len(set(map(encode,POOL))),len(POOL))
    def test_exhaustive_call_count_and_bytes(self):
        names=[Name(x) for x in POOL[:4]]
        for length in range(4):
            for seeds in itertools.product(names,repeat=length):
                for rawlen in range(4):
                    for raw in itertools.product(names,repeat=rawlen):
                        keys=Keys(seeds);got=[keys.get(n) for n in raw]+[keys.get(n) for n in seeds]
                        self.assertEqual(got,[encode(n.value) for n in (*raw,*seeds)])
                        self.assertEqual(keys.encodes,len(set(seeds))+sum(n not in set(seeds) for n in raw))
                        self.assertLessEqual(keys.encodes,len(seeds)+len(raw))
    def test_foreign_equal_names_lookup_only_and_no_region_retention(self):
        env=Name(POOL[2]);foreign=Name(POOL[2],'newly-read');missing=Name(POOL[-1],'newly-read')
        keys=Keys([env]);value=keys.get(foreign);keys.get(missing)
        self.assertIs(next(iter(keys.cache)),env)
        self.assertTrue(all(k.source=='environment' for k in keys.cache))
        self.assertIsInstance(value,bytes);self.assertEqual(value,encode(env.value));self.assertNotIn(missing,keys.cache)
    def test_module_at_a_time_scope_and_auxiliary_fallback(self):
        a,b=map(Name,POOL[2:4]);first=Keys([a]);second=Keys([b])
        self.assertNotIn(a,second.cache);self.assertNotIn(b,first.cache)
        before=dict(first.cache);first.get(b);self.assertEqual(first.cache,before)
    def test_deep_unicode_large_natural_and_zero(self):
        n=ANON
        for i in range(128):n=N(S(n,'段'),i)
        for v in [n,N(ANON,2**2048),S(ANON,'\0é\n')]:
            a=Name(v);self.assertEqual(Keys([a]).get(Name(v,'reader')),encode(v))
    def test_complete_reports_order_counts_and_rejection_differential(self):
        names=list(map(Name,POOL));raw=lambda ns:[Name(n.value,'reader') for n in ns]
        for kinds in itertools.product(['theorem','definition'],repeat=3):
            modules=[]
            for i,kind in enumerate(kinds):
                effective=[(names[2],kind),(names[i],kind),(names[i],kind)]
                parts=[(raw([n for n,_ in effective]),raw([names[-1],names[2]])),([],[]),
                       (raw([n for n,_ in effective]),raw([names[-1]]))]
                modules.append((effective,parts))
            direct,n1=model(modules,False);cached,n2=model(modules,True)
            self.assertEqual(cached,direct);self.assertLess(n2,n1)
            self.assertEqual(cached[-1]['actual'],9);self.assertEqual(cached[-1]['raw'],18)
    def test_malformed_effective_set_still_uses_exact_fallback(self):
        effective=[(Name(POOL[0]),'theorem')];parts=[([Name(POOL[-1],'reader')],[])]
        self.assertEqual(model([(effective,parts)],True)[0],model([(effective,parts)],False)[0])
    def test_stale_or_display_key_substitution_detected(self):
        name=Name(POOL[2]);keys=Keys([name]);keys.cache[name]=b'wrong'
        self.assertNotEqual(keys.get(name),encode(name.value))
        self.assertNotEqual(encode(S(ANON,'0')),encode(N(ANON,0)))

if __name__=='__main__':unittest.main(verbosity=2)
