"""Python model/real telemetry regressions; native Lean fixture is source only.

No compiler, lease or CI is invoked. This is not native classifier acceptance.
The model uses the constructors exercised here; native Expr equality remains
Lean's own BEq and is covered by the unexecuted exact-helper native fixture.
"""
from dataclasses import dataclass,replace
from pathlib import Path
import hashlib,json,re,sys,unittest

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SPEC=json.loads((HERE/'ci-spec.json').read_text())
sys.path.insert(0,str(ROOT/SPEC['engine_directory']))
from collision_coverage import validate_collision_coverage

def const(name,*levels):return ('const',name,levels)
def sort(level=0):return ('sort',level)
def app(fn,arg):return ('app',fn,arg)
def forall(name,domain,body,annotation='default'):return ('forall',name,domain,body,annotation)
def eqv(a,b):
    if a[0]!=b[0]:return False
    if a[0]=='forall':return eqv(a[2],b[2]) and eqv(a[3],b[3])
    if a[0]=='app':return eqv(a[1],b[1]) and eqv(a[2],b[2])
    return a==b

@dataclass(frozen=True)
class Decl:
    name:str
    kind:str='theorem'
    type:tuple=const('True')
    levels:tuple=()
    all:tuple|None=None
    unsafe:bool=False
    body:str='proof A'
    def __post_init__(self):
        if self.all is None:object.__setattr__(self,'all',(self.name,))

def cheap(lookup,ty):
    while ty[0]=='forall':ty=ty[3]
    args=0
    while ty[0]=='app':args+=1;ty=ty[1]
    if ty[0]!='const' or ty[1] not in lookup:return False
    result=lookup[ty[1]].type
    for _ in range(args):
        if result[0]!='forall':return False
        result=result[3]
    return result==sort()

def subsumes(lookup,new,prior):
    if new.name!=prior.name or not eqv(new.type,prior.type) or new.levels!=prior.levels:return False
    if new.kind==prior.kind=='theorem':return new.all==prior.all
    if new.kind=='theorem' and prior.kind=='axiom':return new.all==(prior.name,) and not prior.unsafe
    if new.kind==prior.kind=='axiom':return new.unsafe==prior.unsafe and cheap(lookup,new.type)
    return False

def fold(modules):
    winners={};decisions=[]
    for owner,decls in enumerate(modules):
        for slot,new in enumerate(decls):
            if new.name in winners:
                old,old_owner,_=winners[new.name];lookup={n:r[0] for n,r in winners.items()}
                if subsumes(lookup,new,old):outcome='compatible-update'
                elif subsumes(lookup,old,new):outcome='compatible-retain'
                else:outcome='incompatible'
                decisions.append((new.name,old_owner,owner,outcome))
                if outcome=='compatible-update':winners[new.name]=(new,owner,slot)
            else:winners[new.name]=(new,owner,slot)
    return winners,decisions

def telemetry(modules,extras=None,parts=None):
    extras=extras or [[] for _ in modules];parts=parts or [3 for _ in modules]
    lines=[f'AUDIT-PHASE: collision-start modules={len(modules)}']
    raw_keys={};repeat=0;overlaps=[];decl_events=[];typed={};consts=extra_count=actual_count=0
    for owner,decls in enumerate(modules):
        before=len(decl_events);raw_const=raw_extra=0
        for names,auxes in ([(decls,extras[owner])] if parts[owner]==1 else [(decls,extras[owner]),([],[]),(decls,extras[owner])]):
            for name,auxiliary in [(d.name,False) for d in names]+[(n,True) for n in auxes]:
                if auxiliary:raw_extra+=1
                else:raw_const+=1
                if name in raw_keys:
                    prior,prior_aux=raw_keys[name]
                    if prior==owner:repeat+=1
                    else:
                        category='auxiliary-ownership' if auxiliary or prior_aux else 'constant-name-metadata'
                        lines.append(f'COLLISION-CLAIM: {len(overlaps)} key={name.encode().hex()} prior={prior} owner={owner} class={category}')
                        overlaps.append(category)
                else:raw_keys[name]=(owner,auxiliary)
        consts+=raw_const;extra_count+=raw_extra;local=[]
        for slot,new in enumerate(decls):
            actual_count+=1
            if new.name in typed:
                prior,prior_owner,_=typed[new.name];lookup={n:r[0] for n,r in typed.items()}
                if subsumes(lookup,new,prior):outcome='compatible-update'
                elif subsumes(lookup,prior,new):outcome='compatible-retain'
                else:outcome='incompatible'
                lines.append(f'COLLISION-DECL: {len(decl_events)} key={new.name.encode().hex()} prior={prior_owner} owner={owner} result={outcome}')
                decl_events.append(outcome);local.append(outcome)
                if outcome=='compatible-update':typed[new.name]=(new,owner,slot)
            else:typed[new.name]=(new,owner,slot)
        good=sum(x.startswith('compatible-') for x in local);bad=local.count('incompatible')
        lines.append(f'COLLISION-MODULE: {owner} {parts[owner]} parts, {raw_const} constNames, {raw_extra} extraConstNames, {parts[owner]} regions freed')
        lines.append(f'COLLISION-ACTUAL: {owner} {len(decls)} declarations, {len(decls)} constNames, {len(decl_events)-before} duplicates, {good} compatible, {bad} incompatible, 0 unclassified')
    total=consts+extra_count;read=sum(parts)
    lines.append(f'COLLISION-COVERAGE: {len(modules)} modules, {total} declarations/extra-name claims, {read} parts read, {read} regions freed, {max(parts)} peak owned regions, {len(raw_keys)} independent keys, {consts} constNames, {extra_count} extraConstNames, {repeat} same-module repetitions, {len(overlaps)} cross-module collisions')
    meta=overlaps.count('constant-name-metadata');aux=overlaps.count('auxiliary-ownership');good=sum(x.startswith('compatible-') for x in decl_events);bad=decl_events.count('incompatible')
    lines.append(f'COLLISION-CLASSIFICATION: {meta} constant-name metadata overlaps, {aux} auxiliary ownership overlaps, {actual_count} effective declarations, {actual_count} effective constNames, {len(decl_events)} duplicate declarations, {good} compatible, {bad} incompatible, 0 unclassified, {len(typed)} effective keys')
    return '\n'.join(lines)+'\n'

def native_fixture_source():
    audit=(ROOT/SPEC['sources']['audit']['path']).read_text()
    start=audit.index('/- Verification helper only.')
    boundary=audit.index('end LightEFTAuditCollision')+len('end LightEFTAuditCollision')
    helper=audit[start:boundary]
    tail=(HERE/'CollisionClassifierFixtures.tail.lean').read_text()
    return 'import Lean\n\n'+helper+'\n\n'+tail

class ClassifierModelTests(unittest.TestCase):
    def setUp(self):self.lookup={'True':Decl('True','axiom',sort())}
    def test_generated_equation_congruence_and_arbitrary_theorems(self):
        for name in ['Generated.eq_1','Generated.congr_1','Arbitrary','not_a_pattern']:
            with self.subTest(name=name):
                a=Decl(name);b=replace(a,body='distinct proof B')
                self.assertTrue(subsumes(self.lookup,a,b));self.assertTrue(subsumes(self.lookup,b,a))
    def test_type_levels_mutual_group_and_kind_mismatches(self):
        a=Decl('x')
        variants=[replace(a,name='y'),replace(a,type=const('False')),replace(a,levels=('u',)),
                  replace(a,all=('x','mutual')),replace(a,kind='definition'),replace(a,kind='opaque')]
        for b in variants:
            with self.subTest(variant=b):self.assertFalse(subsumes(self.lookup,a,b));self.assertFalse(subsumes(self.lookup,b,a))
        self.assertFalse(subsumes(self.lookup,replace(a,levels=('u','v')),replace(a,levels=('v','u'))))
    def test_binder_alpha_equivalence_and_no_definitional_reduction(self):
        a=Decl('x',type=forall('a',const('Nat'),const('True')))
        b=replace(a,type=forall('b',const('Nat'),const('True'),'implicit'))
        self.assertTrue(subsumes(self.lookup,a,b))
        self.assertFalse(subsumes(self.lookup,Decl('x'),Decl('x',type=const('ReducibleTrueAlias'))))
    def test_directed_safe_theorem_axiom_and_mutual_rule(self):
        thm=Decl('x');ax=Decl('x','axiom')
        self.assertTrue(subsumes(self.lookup,thm,ax));self.assertFalse(subsumes(self.lookup,ax,thm))
        self.assertFalse(subsumes(self.lookup,thm,replace(ax,unsafe=True)))
        self.assertFalse(subsumes(self.lookup,replace(thm,all=('x','other')),ax))
    def test_axiom_proposition_safety_and_head_arity(self):
        ax=Decl('x','axiom')
        self.assertTrue(subsumes(self.lookup,ax,ax))
        self.assertTrue(subsumes(self.lookup,replace(ax,unsafe=True),replace(ax,unsafe=True)))
        self.assertFalse(subsumes(self.lookup,ax,replace(ax,unsafe=True)))
        self.assertFalse(subsumes({},ax,ax))
        self.assertFalse(subsumes(self.lookup,replace(ax,type=sort()),replace(ax,type=sort())))
        pred=Decl('P','axiom',forall('x',const('Nat'),sort()))
        lookup={'P':pred};self.assertTrue(cheap(lookup,app(const('P'),const('Nat.zero'))))
        self.assertFalse(cheap(lookup,const('P')));self.assertFalse(cheap(lookup,app(app(const('P'),const('Nat.zero')),const('Nat.zero'))))
    def test_definitions_and_opaque_duplicates_always_reject(self):
        for kind in ['definition','opaque','inductive','constructor','recursor','quotient']:
            d=Decl('same',kind)
            with self.subTest(kind=kind):self.assertFalse(subsumes(self.lookup,d,d))
    def test_ordered_replacement_and_future_head_not_visible(self):
        predicate=self.lookup['True'];thm=Decl('x');ax=Decl('x','axiom')
        winner,events=fold([[predicate],[ax],[thm]]);self.assertEqual(winner['x'][1],2);self.assertEqual(events[-1][-1],'compatible-update')
        winner,events=fold([[predicate],[thm],[ax]]);self.assertEqual(winner['x'][1],1);self.assertEqual(events[-1][-1],'compatible-retain')
        _,events=fold([[ax],[ax],[predicate]]);self.assertEqual(events[-1][-1],'incompatible')
    def test_incompatible_pair_does_not_get_hidden_by_later_replacement(self):
        _,events=fold([[Decl('x')],[Decl('x',type=const('False'))],[Decl('x')]])
        self.assertEqual(events[0][-1],'incompatible');self.assertEqual(events[1][-1],'compatible-update')

class TelemetryTests(unittest.TestCase):
    def valid(self):
        return telemetry([[Decl('True','axiom',sort()),Decl('Generated.eq_1')],[Decl('Generated.eq_1',body='B')]],
                         extras=[['auxiliary'],['auxiliary']],parts=[3,1])
    def test_real_parser_accepts_completely_classified_findings(self):
        result=validate_collision_coverage(['A','B'],self.valid())
        self.assertEqual(result['compatible_duplicates'],1)
        self.assertGreater(result['auxiliary_ownership_overlaps'],0)
        self.assertGreater(result['constant_name_metadata_overlaps'],0)
        self.assertEqual(result['owned_regions_freed'],4)
    def test_auxiliary_claims_do_not_populate_actual_constant_map(self):
        raw=telemetry([[],[Decl('same')]],extras=[['same'],[]])
        result=validate_collision_coverage(['A','B'],raw)
        self.assertEqual(result['duplicate_declarations'],0);self.assertEqual(result['effective_declarations'],1)
        self.assertGreater(result['auxiliary_ownership_overlaps'],0)
    def test_same_module_duplicate_definition_is_incompatible(self):
        raw=telemetry([[Decl('same','definition'),Decl('same','definition')]])
        with self.assertRaises(ValueError):validate_collision_coverage(['A'],raw)
    def test_incompatible_and_unclassified_always_reject(self):
        raw=telemetry([[Decl('same')],[Decl('same',type=const('False'))]])
        with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],raw)
        raw=self.valid().replace('COLLISION-MODULE: 0','COLLISION-UNCLASSIFIED: 0 owner=0 scope=raw-name\nCOLLISION-MODULE: 0',1)
        with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],raw)
    def test_every_missing_duplicate_reordered_or_malformed_marker_rejects(self):
        raw=self.valid();lines=raw.splitlines()
        for i,line in enumerate(lines):
            with self.subTest(mutation='missing',line=i):
                with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],'\n'.join(lines[:i]+lines[i+1:])+'\n')
            with self.subTest(mutation='duplicated',line=i):
                with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],'\n'.join(lines[:i]+[line]+lines[i:])+'\n')
            with self.subTest(mutation='suffix',line=i):
                changed=lines.copy();changed[i]+=' junk'
                with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],'\n'.join(changed)+'\n')
        with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],raw.rstrip('\n'))
        with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],raw+'COLLISION-UNKNOWN: 0\n')
        for i in range(len(lines)-1):
            changed=lines.copy();changed[i],changed[i+1]=changed[i+1],changed[i]
            # Different event kinds within one module may legitimately commute;
            # only swap fixed boundary/start/summary positions in this check.
            if not (lines[i].startswith(('AUDIT-PHASE','COLLISION-MODULE','COLLISION-ACTUAL','COLLISION-COVERAGE')) or
                    lines[i+1].startswith(('COLLISION-MODULE','COLLISION-ACTUAL','COLLISION-COVERAGE'))):continue
            with self.subTest(mutation='swap',line=i):
                with self.assertRaises(ValueError):validate_collision_coverage(['A','B'],'\n'.join(changed)+'\n')
    def test_counter_scope_key_and_classification_mutations_reject(self):
        raw=self.valid()
        changes=[('4 parts read','5 parts read'),('4 regions freed','3 regions freed'),
          ('3 peak owned regions','4 peak owned regions'),('compatible-update','incompatible'),
          ('class=auxiliary-ownership','class=unclassified'),('result=compatible-update','result=whitelisted'),
          ('owner=1','owner=2'),('COLLISION-CLAIM: 0','COLLISION-CLAIM: 7'),
          ('key=617578696c69617279','key=0'),('1 compatible, 0 incompatible','0 compatible, 0 incompatible')]
        for old,new in changes:
            self.assertIn(old,raw)
            with self.subTest(old=old,new=new),self.assertRaises(ValueError):
                validate_collision_coverage(['A','B'],raw.replace(old,new,1))

class SourceTests(unittest.TestCase):
    def test_native_fixture_uses_exact_production_helper_and_no_paper_import(self):
        source=native_fixture_source()
        self.assertTrue(source.startswith('import Lean\n'))
        self.assertNotIn('import LightEFTJointFlagSamplingStage',source)
        self.assertIn('def subsumesInfo',source);self.assertIn('Generated "congr_1"',source)
        self.assertIn('Lean.Meta.getEqnsFor?',source);self.assertIn('Lean.Meta.mkCongrSimp?',source)
        self.assertIn('CLASSIFIER-NATIVE-FIXTURES: passed',source)
    def test_no_borrowed_metadata_in_state_and_no_name_whitelist(self):
        source=(ROOT/SPEC['sources']['audit']['path']).read_text()
        state=source.split('structure State where',1)[1].split('/- Same predicate',1)[0]
        for forbidden in ['ConstantInfo','Expr','ModuleData','Array Name']:
            self.assertNotIn(forbidden,state)
        predicate=source.split('def subsumesInfo',1)[1].split('private def infoAt',1)[0]
        for required in ['new.type == prior.type','new.levelParams == prior.levelParams','a.all == b.all','a.all == [b.name]','a.isUnsafe == b.isUnsafe','isPropCheap lookup a.type']:
            self.assertIn(required,predicate)
        for forbidden in ['.value','Generated','congr','eq_1','isDefEq']:
            self.assertNotIn(forbidden,predicate)
        self.assertIn('let data := env.header.moduleData',source)
        self.assertIn('let lookup := lookupDeclaration data state',source)
        self.assertNotIn('env.find?',source[:source.index('end LightEFTAuditCollision')])

if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--write-native-source':
        path=Path(sys.argv[2]);path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():raise RuntimeError('Refuse fixture source overwrite')
        path.write_text(native_fixture_source());print(json.dumps(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),executed=False)))
    else:unittest.main(verbosity=2)
