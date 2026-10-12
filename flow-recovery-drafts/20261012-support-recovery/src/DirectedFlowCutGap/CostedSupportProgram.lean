import DirectedFlowCutGap.ActualSupportSearch
import DirectedFlowCutGap.RecoveredEdgeProjection

/-! One table calls physical support search, projects its returned edge list,
materializes and sums the original graph's outgoing row costs, and allocates
one result record retaining those exact recovered edges. -/
namespace DirectedFlowCutGap.CostedSupportProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

def searchLabel (pc : Fin 280) : Fin 592 := ⟨pc.val,by omega⟩
def projectLabel (pc : Fin 12) : Fin 592 := ⟨pc.val+280,by omega⟩
def sumLabel (pc : Fin 284) : Fin 592 := ⟨pc.val+292,by omega⟩
def program : Program 592 := fun pc =>
  if pc.val=279 ∨ pc.val=291 ∨ pc.val=575 then .ret .r3
  else if h : pc.val<280 then
    ReferenceProgramLabels.instruction searchLabel (SupportRecoveryProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<292 then
    ReferenceProgramLabels.instruction projectLabel (RecoveredEdgeProjection.program ⟨pc.val-280,by omega⟩)
  else if h : pc.val<576 then
    ReferenceProgramLabels.instruction sumLabel (MaterializedPathSum.program ⟨pc.val-292,by omega⟩)
  else match pc.val with
  | 576 => .call 580 577 .r3
  | 577 => .make .r2 (.pair .r3 .r1) 578
  | 578 => .move .r0 .r3 579
  | 579 => .call 290 583 .r3
  | 580 => .field .r1 .r1 false 581
  | 581 => .call 270 582 .r3
  | 582 => .ret .r3
  | 583 => .move .r0 .r3 584
  | 584 => .field .r1 .r2 true 585
  | 585 => .field .r1 .r1 true 586
  | 586 => .call 574 587 .r3
  | 587 => .field .r0 .r2 false 588
  | 588 => .make .r3 (.pair .r0 .r3) 589
  | 589 => .ret .r3
  | 590 => .call 576 591 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 592)) (source : Bits) (pc : Fin 592) : NaturalState 592 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def Context (heap : NaturalHeap) (root : ℕ) (vs adjacency : List Bits)
    (es : List (Bits×Bits)) (target : Bits) (rows : List Fraction) (sw : Bits) : Prop :=
  ∃ search costs,heap[root]?=some (.pair search costs) ∧
    SupportRecoveryProgram.StoredGlobalContext heap search vs adjacency es target ∧
    OutgoingCostProgram.Context heap costs rows sw

def edges (vs adjacency : List Bits) (es : List (Bits×Bits)) (sw target : Bits) :=
  SupportRecoveryProgram.search vs adjacency es sw target

def result (vs adjacency : List Bits) (es : List (Bits×Bits)) (sw target : Bits)
    (rows : List Fraction) : Walk :=
  ⟨edges vs adjacency es sw target,MaterializedPathSum.result rows sw ((edges vs adjacency es sw target).map Prod.fst)⟩

def steps (vs adjacency : List Bits) (es : List (Bits×Bits)) (sw target : Bits)
    (rows : List Fraction) : ℕ :=
  SupportRecoveryProgram.searchSteps vs adjacency es sw target+
    7*(edges vs adjacency es sw target).length+
    MaterializedPathSum.steps rows sw ((edges vs adjacency es sw target).map Prod.fst)+23

def cells (vs adjacency : List Bits) (es : List (Bits×Bits)) (sw target : Bits)
    (rows : List Fraction) : ℕ :=
  SupportRecoveryProgram.searchCells vs adjacency es sw target+
    (edges vs adjacency es sw target).length+
    MaterializedPathSum.cells rows sw ((edges vs adjacency es sw target).map Prod.fst)+2

theorem context_extend {heap : NaturalHeap} {root : ℕ} {vs adjacency : List Bits}
    {es : List (Bits×Bits)} {target sw : Bits} {rows : List Fraction}
    (h : Context heap root vs adjacency es target rows sw) (ext : NaturalHeap) :
    Context (heap++ext) root vs adjacency es target rows sw := by
  obtain ⟨s,c,hp,hs,hc⟩ := h
  exact ⟨s,c,lookup_extend hp ext,SupportRecoveryProgram.globalContext_extend hs ext,
    PathCostMaterialization.context_extend hc ext⟩

theorem search_slots (pc : Fin 280) (h : SupportRecoveryProgram.program pc≠.halt) :
    program (searchLabel pc)=ReferenceProgramLabels.instruction searchLabel (SupportRecoveryProgram.program pc) := by
  by_cases hp : pc.val=279
  · have he : pc=279 := Fin.ext hp
    subst pc;simp [SupportRecoveryProgram.program] at h
  · simp [program,searchLabel,pc.isLt,hp,show ¬pc.val=291 by omega,show ¬pc.val=575 by omega]

theorem project_slots (pc : Fin 12) (h : RecoveredEdgeProjection.program pc≠.halt) :
    program (projectLabel pc)=ReferenceProgramLabels.instruction projectLabel (RecoveredEdgeProjection.program pc) := by
  by_cases hp : pc.val=11
  · have he : pc=11 := Fin.ext hp
    subst pc;simp [RecoveredEdgeProjection.program] at h
  · simp [program,projectLabel,show ¬pc.val+280=279 by omega,show ¬pc.val+280=291 by omega,
      show ¬pc.val+280=575 by omega,show ¬pc.val+280<280 by omega,show pc.val+280<292 by omega]

theorem sum_slots (pc : Fin 284) (h : MaterializedPathSum.program pc≠.halt) :
    program (sumLabel pc)=ReferenceProgramLabels.instruction sumLabel (MaterializedPathSum.program pc) := by
  by_cases hp : pc.val=283
  · have he : pc=283 := Fin.ext hp
    subst pc;simp [MaterializedPathSum.program] at h
  · simp [program,sumLabel,show ¬pc.val+292=279 by omega,show ¬pc.val+292=291 by omega,
      show ¬pc.val+292=575 by omega,show ¬pc.val+292<280 by omega,
      show ¬pc.val+292<292 by omega,show pc.val+292<576 by omega]

theorem run_append {s u v : NaturalState 592} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.CostedSupportProgram
