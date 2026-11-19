import DirectedFlowCutGap.InitialDemandFlagProgram
import DirectedFlowCutGap.DemandQueryContext

/-! Load the actual source and target and build the shortest-path query on the same heap. -/

namespace DirectedFlowCutGap.InitialDemandPairProgram

open BooleanTableRead (BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open RetainedGridState (PairFlags Pair flag)
open ConcreteExpressionProgram (append_run)
open GraphWalkExtension (Edge)
open InitialDemandFlagProgram (units)
open IntegerDistanceFromPhysical (encodedRow)

def contextLabel (pc : Fin 1604) : Fin 3060 := if pc.val=1603 then 1 else ⟨32+pc.val,by omega⟩
def flagLabel (pc : Fin 1424) : Fin 3060 := ⟨1636+pc.val,by omega⟩

def program : Program 3060 := fun pc =>
  if pc.val < 32 then
    match pc.val with
    | 0 => .call (contextLabel 1580) 1 .r3
    | 1 => .field .r0 .r0 false 2
    | 2 => .make .r3 (.pair .r3 .r2) 3
    | 3 => .move .r2 .r0 4
    | 4 => .field .r0 .r1 false 5
    | 5 => .field .r1 .r3 false 6
    | 6 => .field .r3 .r3 true 7
    | 7 => .call (flagLabel 0) 8 .r3
    | _ => .halt
  else if h : pc.val < 1636 then
    ReferenceProgramLabels.instruction contextLabel (DemandCollection.program ⟨pc.val-32,by omega⟩)
  else if pc.val=1646 then .ret .r3
  else ReferenceProgramLabels.instruction flagLabel (InitialDemandFlagProgram.program ⟨pc.val-1636,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 3060

private theorem context_slots (pc : Fin 1604) (h : DemandCollection.program pc≠.halt) :
    program (contextLabel pc)=ReferenceProgramLabels.instruction contextLabel (DemandCollection.program pc) := by
  by_cases stop : pc.val=1603
  · have eq : pc=1603 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,contextLabel,stop,show ¬32+pc.val<32 by omega,show 32+pc.val<1636 by omega]

private theorem flag_slots (pc : Fin 1424) (h : InitialDemandFlagProgram.program pc≠.halt) :
    program (flagLabel pc)=ReferenceProgramLabels.instruction flagLabel (InitialDemandFlagProgram.program pc) := by
  by_cases stop : pc.val=10
  · have eq : pc=10 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,flagLabel,show ¬1636+pc.val<32 by omega,show ¬1636+pc.val<1636 by omega,show 1636+pc.val≠1646 by omega]

private theorem load_query {heap : NaturalHeap} {r : Registers ℕ} {s t : Bits} {vs adjacency : List Bits}
    {rows : List BinaryRational.Fraction}
    (key : Edge heap r.a (s,t)) (shared : DemandCollection.Shared heap r.b vs adjacency rows) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency rows s t ∧
      NaturalRun program 13 (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let x : DemandCollection.Demand := ⟨s,t,r.a,0⟩
  obtain ⟨ext,root,count,work,rep⟩ := DemandCollection.build_query_context (x:=x) key shared
    heap.length r.c r.d rfl r 1603 [] tape
  have concrete := ReferenceProgramLabels.run contextLabel DemandCollection.program program context_slots work
  have first : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [⟨1,.r3,r⟩] tape (contextLabel 1580),[],0⟩ := rfl
  have run : NaturalRun program 12 (state heap r [⟨1,.r3,r⟩] tape (contextLabel 1580)) []
      (state (heap++ext) (r.set .r3 root) [] tape 1) := by
    cases r
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramInvocation.state,
      DemandCollection.state,x,Registers.set,count,contextLabel] using concrete
  exact ⟨ext,root,rep,.step first run⟩

set_option maxHeartbeats 2300000 in
private theorem prepare_args {heap : NaturalHeap} {r : Registers ℕ} {s t level : Bits} {vs adjacency : List Bits}
    {rows : List BinaryRational.Fraction} {root : ℕ}
    (key : Edge heap r.a (s,t)) (shared : DemandCollection.Shared heap r.b vs adjacency rows)
    (threshold : BoolList heap r.c level)
    (query : GraphDiscoveryProgram.GlobalContext heap root vs adjacency rows s t) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ),
      GraphDiscoveryProgram.Vertices (heap++ext) args.a vs ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) args.b vs adjacency rows s t ∧
      BoolList (heap++ext) args.c s ∧ BoolList (heap++ext) args.d level ∧
      NaturalRun program 6 (state heap (r.set .r3 root) [] tape 1) []
        (state (heap++ext) args [] tape 7) := by
  obtain ⟨source,target,pair,hs,ht⟩ := key
  obtain ⟨enum,bundle,matrix,fields,atShared,atBundle,en,ar,tab⟩ := shared
  let entry : Registers ℕ := ⟨source,r.b,r.c,root⟩
  have read : tickNatural program (state heap (r.set .r3 root) [] tape 1)=some ⟨state heap entry [] tape 2,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,pair,entry]
  let packet : Cell ℕ := .pair root r.c
  let ext : NaturalHeap := [packet]
  let mid := heap++ext
  let next : Registers ℕ := ⟨source,r.b,source,heap.length⟩
  have save : NaturalRun program 2 (state heap entry [] tape 2) [] (state mid next [] tape 4) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      entry,next,mid,ext,packet,allocateNatural,Recipe.cell]
  let args : Registers ℕ := ⟨enum,root,source,r.c⟩
  have atConfig : mid[r.b]?=some (.pair enum bundle) := lookup_extend atShared ext
  have pack : mid[heap.length]?=some packet := by simp [mid,ext]
  have fields : NaturalRun program 3 (state mid next [] tape 4) [] (state mid args [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      next,args,atConfig,pack,packet]
  exact ⟨ext,args,GraphDiscoveryProgram.vertices_extend en ext,GraphDiscoveryProgram.global_extend query ext,
    boolList_extend hs ext,boolList_extend threshold ext,.step read (append_run save fields)⟩

theorem natural_pair {n W : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (p : Pair n) (label : Fin n→Bits) (labels : ∀ i,value (label i)=i.val)
    (level : Bits) (key : Edge heap r.a (label p.1,label p.2))
    (shared : DemandCollection.Shared heap r.b (E.vertices.map label) (GraphRelaxationRefinement.matrix adj) (encodedRow (units n)).toList)
    (threshold : BoolList heap r.c level) (hW : 1≤W) (labelWidth : ∀ i,(label i).length≤W) (levelWidth : level.length≤W)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root a b c k : ℕ),
      (heap++ext)[root]?=some (.flag (flag (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)) p)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) ⟨a,b,c,root⟩ [] tape 8) ∧
      k≤ InitialDemandFlagProgram.instructionBound n W (label p.1).length+21 := by
  obtain ⟨ec,query,rep,contextCall⟩ := load_query key shared tape
  obtain ⟨ep,args,inList,inCtx,sourceRep,levelRep,loaded⟩ :=
    prepare_args (GraphWalkExtension.edge_extend key ec) (DemandCollection.shared_extend shared ec)
      (boolList_extend threshold ec) rep tape
  obtain ⟨ef,root,a,b,k,answer,body,time⟩ := InitialDemandFlagProgram.natural_flag E adj p.1 p.2
    (label p.1) (labels p.1) label labels level inList inCtx sourceRep levelRep hW (labelWidth p.1) labelWidth levelWidth tape
  have invoke := ReferenceProgramInvocation.call flagLabel flag_slots (caller:=7) (continuation:=8)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] body
  refine ⟨ec++ep++ef,root,args.a,args.b,args.c,13+(6+(k+2)),?_,?_,by omega⟩
  · simpa only [List.append_assoc,Prod.mk.eta] using answer
  · simpa only [Registers.get,Registers.set,List.append_assoc,List.nil_append] using append_run contextCall (append_run loaded invoke)

end DirectedFlowCutGap.InitialDemandPairProgram
