import DirectedFlowCutGap.WordPairProductProgram
import DirectedFlowCutGap.InitialRetainedStateProgram

/-! Build stored original vertex and pair labels from the original dimension word. -/

namespace DirectedFlowCutGap.InitialGraphDictionary

open BooleanTableRead (BoolList IndexSpine)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList list_extend)
open GraphWalkExtension (EdgeList edgeList_extend)
open EpochActiveFromMaskProgram (labelPair)

def rangeLabel (pc : Fin 65) : Fin 129 := ⟨32+pc.val,by omega⟩
def productLabel (pc : Fin 32) : Fin 129 := ⟨97+pc.val,by omega⟩

def program : Program 129 := fun pc =>
  if pc.val < 32 then
    match pc.val with
    | 0 => .call (rangeLabel 0) 1 .r0
    | 1 => .move .r1 .r0 2
    | 2 => .call (productLabel 0) 3 .r1
    | 3 => .make .r3 (.pair .r0 .r1) 4
    | _ => .halt
  else if h : pc.val < 97 then
    if pc.val=36 then .ret .r3
    else ReferenceProgramLabels.instruction rangeLabel (BinaryLabelRangeProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=99 then .ret .r3
  else ReferenceProgramLabels.instruction productLabel (WordPairProductProgram.program ⟨pc.val-97,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 129

abbrev label {n : ℕ} (i : Fin n) : Bits := i.val.bits
abbrev labels (n : ℕ) := (List.finRange n).map label

theorem as_vertices {heap : NaturalHeap} {root : ℕ} {words : List Bits} (h : WordList heap root words) :
    GraphDiscoveryProgram.Vertices heap root words := by
  induction h with
  | nil atNil => exact .nil atNil
  | cons pair word _ ih => exact .cons pair word ih

theorem word_spine {heap : NaturalHeap} {root : ℕ} {words : List Bits} (h : WordList heap root words) :
    IndexSpine heap root words.length := by
  induction h with
  | nil atNil => exact .nil atNil
  | cons pair _ _ ih => exact .cons pair ih

theorem edge_spine {heap : NaturalHeap} {root : ℕ} {words : List (Bits×Bits)} (h : EdgeList heap root words) :
    IndexSpine heap root words.length := by
  induction h with
  | nil atNil => exact .nil atNil
  | cons pair _ _ ih => exact .cons pair ih

theorem pair_words (n : ℕ) : (labels n).product (labels n)=(RetainedMassTableProgram.pairOrder n).map labelPair := by
  simp [labels,RetainedMassTableProgram.pairOrder,List.product,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,labelPair]

private theorem range_slots (pc : Fin 65) (h : BinaryLabelRangeProgram.program pc≠.halt) :
    program (rangeLabel pc)=ReferenceProgramLabels.instruction rangeLabel (BinaryLabelRangeProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,rangeLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<97 by omega,show 32+pc.val≠36 by omega]

private theorem product_slots (pc : Fin 32) (h : WordPairProductProgram.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (WordPairProductProgram.program pc) := by
  by_cases stop : pc.val=2
  · have eq : pc=2 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,productLabel,show ¬97+pc.val<32 by omega,show ¬97+pc.val<97 by omega,show 97+pc.val≠99 by omega]

def steps (n : ℕ) (count : Bits) : ℕ := BinaryLabelRangeProgram.steps count+WordPairProductProgram.steps n n+6

theorem steps_le (count : Bits) (n : ℕ) (size : value count=n) :
    steps n count ≤ n*(8*n.size+19)+10*count.length+WordPairProductProgram.steps n n+15 := by
  have h := BinaryLabelRangeProgram.steps_le count
  rw [size] at h
  unfold steps
  omega

theorem natural_dictionary {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {count : Bits}
    (stored : BoolList heap r.a count) (size : value count=n) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root vertices pairs : ℕ),
      (heap++ext)[root]?=some (.pair vertices pairs) ∧ WordList (heap++ext) vertices (labels n) ∧
      EdgeList (heap++ext) pairs ((RetainedMassTableProgram.pairOrder n).map labelPair) ∧
      NaturalRun program (steps n count) (state heap r [] tape 0) []
        (state (heap++ext) ⟨vertices,pairs,r.c,root⟩ [] tape 4) := by
  obtain ⟨ev,vr,vertices,list,body⟩ := BinaryLabelRangeProgram.natural_range stored tape
  let mid := heap++ev
  let first := r.set .r0 vertices
  let args := first.set .r1 vertices
  have labelsAt : WordList mid vertices (labels n) := by
    rw [size,BinaryLabelRangeProgram.words_fin] at list
    exact list
  have load := ReferenceProgramInvocation.call rangeLabel range_slots (caller:=0) (continuation:=1)
    (dst:=.r0) (result:=.r3) (by rfl) (by rfl) [] body
  have copy : tickNatural program (state mid first [] tape 1)=some ⟨state mid args [] tape 2,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,first]
  obtain ⟨ep,pr,pairs,pairAt,product⟩ := WordPairProductProgram.natural_product (r:=args) labelsAt labelsAt tape
  have call := ReferenceProgramInvocation.call productLabel product_slots (caller:=2) (continuation:=3)
    (dst:=.r1) (result:=.r3) (by rfl) (by rfl) [] product
  have len : (labels n).length=n := by simp [labels]
  rw [len] at call
  let grown := mid++ep
  let record : Cell ℕ := .pair vertices pairs
  let out : Registers ℕ := ⟨vertices,pairs,r.c,grown.length⟩
  have finish : tickNatural program (state grown (args.set .r1 pairs) [] tape 3)=
      some ⟨state (grown++[record]) out [] tape 4,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,first,out,record,allocateNatural,Recipe.cell]
  have loc : (grown++[record])[grown.length]?=some record := by simp
  refine ⟨ev++ep++[record],grown.length,vertices,pairs,?_,?_,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc,record] using loc
  · simpa only [grown,mid,List.append_assoc] using list_extend (list_extend labelsAt ep) [record]
  · simpa only [grown,mid,List.append_assoc,pair_words] using edgeList_extend pairAt [record]
  · let x := BinaryLabelRangeProgram.steps count
    let y := WordPairProductProgram.steps n n
    have runs : NaturalRun program (x+2+(y+2+1+1)) (state heap r [] tape 0) []
        (state (grown++[record]) out [] tape 4) := by
      simpa only [x,y,mid,grown,first,args,Registers.get,Registers.set,List.nil_append,List.append_nil,Nat.zero_add] using
        append_run load (.step copy (append_run call (.step finish (.done _))))
    have countEq : x+2+(y+2+1+1)=steps n count := by unfold steps; omega
    rw [← countEq]
    simpa only [grown,mid,out,List.append_assoc] using runs

end DirectedFlowCutGap.InitialGraphDictionary
