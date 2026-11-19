import DirectedFlowCutGap.IntegerLevelVertexProgram
import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.ReferenceProgramSteps
import DirectedFlowCutGap.RetainedDemandMask

/-! Test an original threshold demand from its actual unit-cost shortest path. -/

namespace DirectedFlowCutGap.InitialDemandFlagProgram

open BooleanTableRead (BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open RetainedGridState (Row PairFlags flag)
open ConcreteExpressionProgram (append_run)
open IntegerDistanceFromPhysical (encodedRow interpret)

def graphLabel (pc : Fin 1344) : Fin 1424 := ⟨32+pc.val,by omega⟩
def compareLabel (pc : Fin 48) : Fin 1424 := ⟨1376+pc.val,by omega⟩

def program : Program 1424 := fun pc =>
  if pc.val < 32 then
    match pc.val with
    | 0 => .call (graphLabel 1342) 1 .r0
    | 1 => .branch .r0 8 31 31 2
    | 2 => .field .r1 .r0 true 3
    | 3 => .field .r1 .r1 false 4
    | 4 => .move .r0 .r3 5
    | 5 => .call (compareLabel 30) 10 .r3
    | 8 => .make .r3 (.flag true) 10
    | _ => .halt
  else if h : pc.val < 1376 then
    if pc.val=1375 then .ret .r3
    else ReferenceProgramLabels.instruction graphLabel (GraphRecoveryController.program ⟨pc.val-32,by omega⟩)
  else if pc.val=1422 then .ret .r3
  else ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program ⟨pc.val-1376,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 1424
abbrev units (n : ℕ) : Row n := Vector.replicate n 1

def test (level : Bits) : Option GraphWalkExtension.Walk → Bool
  | none => true
  | some w => (lessEqual level w.cost.num).1

theorem test_correct (level : Bits) (out : Option GraphWalkExtension.Walk) :
    test level out=decide ((value level : WithTop ℕ)≤ interpret out) := by
  cases out with
  | none =>
    change true=decide ((value level : WithTop ℕ)≤⊤)
    simp
  | some q =>
    change (lessEqual level q.cost.num).1=decide ((value level : WithTop ℕ)≤ (value q.cost.num : WithTop ℕ))
    apply Bool.eq_iff_iff.mpr
    simp [(lessEqual_spec level q.cost.num).1]

private theorem graph_slots (pc : Fin 1344) (h : GraphRecoveryController.program pc≠.halt) :
    program (graphLabel pc)=ReferenceProgramLabels.instruction graphLabel (GraphRecoveryController.program pc) := by
  by_cases stop : pc.val=1343
  · have eq : pc=1343 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,graphLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<1376 by omega,show 32+pc.val≠1375 by omega]

private theorem compare_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (compareLabel pc)=ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program pc) := by
  by_cases stop : pc.val=46
  · have eq : pc=46 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,compareLabel,show ¬1376+pc.val<32 by omega,show ¬1376+pc.val<1376 by omega,show 1376+pc.val≠1422 by omega]

def tailSteps (level : Bits) : Option GraphWalkExtension.Walk → ℕ
  | none => 2
  | some w => BinaryComparisonProgram.steps level w.cost.num+9

set_option maxHeartbeats 2500000 in
private theorem compare_distance {heap : NaturalHeap} {r : Registers ℕ} {level : Bits}
    {dist : Option GraphWalkExtension.Walk} (path : GraphDiscoveryProgram.StoredOption heap r.a dist)
    (bound : BoolList heap r.d level) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root a b : ℕ),(heap++ext)[root]?=some (.flag (test level dist)) ∧
      NaturalRun program (tailSteps level dist) (state heap r [] tape 1) [] (state (heap++ext) ⟨a,b,r.c,root⟩ [] tape 10) := by
  cases dist with
  | none =>
    have noneAt : heap[r.a]?=some .nil := path
    let ext : NaturalHeap := [.flag true]
    refine ⟨ext,heap.length,r.a,r.b,by simp [ext,test],?_⟩
    apply ReferenceProgramSteps.sound
    simp [tailSteps,ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,
      Registers.set,tagBranch,noneAt,ext,allocateNatural,Recipe.cell]
  | some w =>
    obtain ⟨edges,cost,atPath,es,num,den,atCost,hn,hd⟩ := path
    let args : Registers ℕ := ⟨r.d,num,r.c,r.d⟩
    have load : NaturalRun program 4 (state heap r [] tape 1) [] (state heap args [] tape 5) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,
        Registers.set,tagBranch,atPath,atCost,args]
    let start : NaturalState 48 := ReferenceProgramInvocation.state heap args [] tape 30
    obtain ⟨out,run,answer,_,_,aEq,bEq,cEq,stackEq,sourceEq,pcEq,nextEq,⟨ext,heapEq,_⟩,_⟩ :=
      BinaryComparisonProgram.compare_high start rfl rfl bound hn rfl
    let root := out.registers.d
    have final : out=ReferenceProgramInvocation.state (heap++ext) (args.set .r3 root) [] tape 46 := by
      rcases out with ⟨h,next,x,stack,pc,source⟩
      rcases x with ⟨a,b,c,d⟩
      simp_all [root,start,ReferenceProgramInvocation.state,Registers.set]
    rw [final] at run answer
    have concrete := ReferenceProgramInvocation.call compareLabel compare_slots (caller:=5) (continuation:=10)
      (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] run
    refine ⟨ext,root,r.d,num,?_,?_⟩
    · simpa only [test,ReferenceProgramInvocation.state,Registers.set] using answer
    · have stepCount : 4+(BinaryComparisonProgram.steps level w.cost.num+3+2)=tailSteps level (some w) := by simp [tailSteps]; omega
      rw [← stepCount]
      simpa only [args,Registers.get,Registers.set,List.nil_append] using append_run load concrete

def instructionBound (n W S : ℕ) : ℕ :=
  GraphRecoveryController.instructionBound n W S+16*(n*(W+2)+W+2)+11

set_option maxHeartbeats 2600000 in
theorem natural_flag {n W : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : ResidualSearch.Enumeration (Fin n)) (adj : PairFlags n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n→Bits) (labels : ∀ i,value (label i)=i.val) (level : Bits)
    (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext heap r.b (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adj) (encodedRow (units n)).toList sw (label t))
    (source : BoolList heap r.c (label s)) (threshold : BoolList heap r.d level)
    (hW : 1≤W) (sourceWidth : sw.length≤W) (labelWidth : ∀ i,(label i).length≤W) (levelWidth : level.length≤W)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root a b k : ℕ),
      (heap++ext)[root]?=some (.flag (flag (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)) (s,t))) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) ⟨a,b,r.c,root⟩ [] tape 10) ∧
      k≤ instructionBound n W sw.length := by
  let y := encodedRow (units n)
  let vs := E.vertices.map label
  let mat := GraphRelaxationRefinement.matrix adj
  let start : NaturalState 1344 := ReferenceProgramInvocation.state heap r [] tape 1342
  have rows : n≤mat.length := by simp [mat,GraphRelaxationRefinement.matrix_length]
  have cols (i : ℕ) (hi : i<n) : n≤(mat[i]'(hi.trans_le rows)).length :=
    (GraphRelaxationRefinement.matrix_row_length adj ⟨i,hi⟩).ge
  have range (u : Bits) (h : u∈vs) : value u<n := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    rw [labels]
    exact i.isLt
  have ht : value (label t)<n := by rw [labels]; exact t.isLt
  have priceRange (u : Bits) (h : u∈vs) : value u<y.toList.length := by
    simpa only [Vector.length_toList] using range u h
  obtain ⟨eg,path,_,raw,result⟩ := GraphRecoveryController.shortest_high n start rfl rfl rfl input context source
    rows cols range ht priceRange (GraphRecoveryController.recovery_valid E adj y s t sw hs label labels)
  let recovered := IntegerLevelVertexProgram.witness E adj (units n) s t label
  have appropriate : GraphDiscoveryProgram.StoredOption (heap++eg) path recovered := by
    change GraphDiscoveryProgram.StoredOption (heap++eg) path (GraphRecoveryController.result vs mat y.toList sw (label t) (label s)) at result
    rw [GraphRecoveryController.result_eq E adj y s t sw hs label labels] at result
    exact result
  let k := GraphRecoveryController.steps vs mat y.toList sw (label t) (label s)+1
  have body : NaturalRun GraphRecoveryController.program k start []
      (ReferenceProgramInvocation.state (heap++eg) (r.set .r3 path) [] tape 1343) := by
    simpa only [start,k,ReferenceProgramInvocation.state,GraphRecoveryController.state,Registers.set,List.length_append] using raw
  have invoke := ReferenceProgramInvocation.call graphLabel graph_slots (caller:=0) (continuation:=1)
    (result:=.r3) (dst:=.r0) (by rfl) (by rfl) [] body
  have called : NaturalRun program (k+2) (state heap r [] tape 0) []
      (state (heap++eg) (r.set .r0 path) [] tape 1) := by
    simpa only [Registers.get,Registers.set] using invoke
  obtain ⟨ef,root,a,b,answer,comparison⟩ := compare_distance (r:=r.set .r0 path) appropriate
    (boolList_extend threshold eg) tape
  have flagValue : test level recovered =
      flag (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)) (s,t) := by
    rw [test_correct,IntegerLevelVertexProgram.witness_value,EncodedIntegerShortestPaths.distance_value]
    simp [flag,RetainedDemandMask.compute,units]
  have unitWidth (i : Fin n) : ((units n)[i.val]).bits.length≤W := by simpa [units] using hW
  have stored := IntegerDistanceFromPhysical.encodedRow_stored (units n) W hW unitWidth
  have graphTime : k≤ GraphRecoveryController.instructionBound n W sw.length :=
    GraphRecoveryController.steps_bound E adj y s t sw hs label labels W hW sourceWidth labelWidth stored
  have each : ∀ i,BinaryRational.StoredBounded (BinaryFractionalRows.get y i) W := by
    intro i
    apply stored
    simp only [y,encodedRow,Vector.toList_ofFn,List.mem_ofFn,BinaryFractionalRows.get,Vector.getElem_ofFn]
    exact ⟨i,rfl⟩
  have shortest := BinaryFractionalWalkBounds.shortest_stored E adj (BinaryFractionalGraphOracle.outgoing y s)
    (BinaryFractionalGraphBounds.outgoing_stored y each s) s t
  have cmpBound : tailSteps level recovered≤ 16*(n*(W+2)+W+2)+9 := by
    cases h : recovered with
    | none => simp [tailSteps]
    | some w =>
      have q : w∈recovered := h
      obtain ⟨p,hp,eq⟩ := Option.mem_map.mp q
      have numWidth : w.cost.num.length≤n*(W+2)+1 := by
        rw [← eq]
        exact (shortest p (Option.mem_def.mp hp)).1
      have cmp := BinaryComparisonProgram.steps_bound level w.cost.num
      simp only [tailSteps]
      omega
  refine ⟨eg++ef,root,a,b,k+2+tailSteps level recovered,?_,?_,?_⟩
  · simpa only [List.append_assoc,flagValue] using answer
  · simpa only [Registers.set,List.append_assoc,List.nil_append] using append_run called comparison
  · unfold instructionBound
    omega

end DirectedFlowCutGap.InitialDemandFlagProgram
