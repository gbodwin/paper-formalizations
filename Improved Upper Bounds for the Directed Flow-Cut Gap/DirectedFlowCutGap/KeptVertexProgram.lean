import DirectedFlowCutGap.PackingZeroMaskRefinement

namespace DirectedFlowCutGap.KeptVertex
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
abbrev same := SupportRecoveryProgram.same

def Context (heap : NaturalHeap) (p : ℕ) (s t : Bits) (zero : Bool) : Prop :=
  ∃ endpoints sr tr flag,heap[p]?=some (.pair endpoints flag) ∧
    heap[endpoints]?=some (.pair sr tr) ∧ BoolList heap sr s ∧ BoolList heap tr t ∧
    heap[flag]?=some (.flag zero)

theorem context_extend {heap : NaturalHeap} {p : ℕ} {s t : Bits} {zero : Bool}
    (h : Context heap p s t zero) (extra : NaturalHeap) : Context (heap++extra) p s t zero := by
  obtain ⟨ep,sr,tr,f,hp,he,hs,ht,hf⟩ := h
  exact ⟨ep,sr,tr,f,PackedBooleanConstructor.lookup_extend hp extra,
    PackedBooleanConstructor.lookup_extend he extra,PackedBooleanConstructor.boolList_extend hs extra,
    PackedBooleanConstructor.boolList_extend ht extra,PackedBooleanConstructor.lookup_extend hf extra⟩

def endpoint (s t u : Bits) : Bool := if same u s then true else same u t

def bit (s t u : Bits) (zero : Bool) : Bool := !zero || same u s || same u t

def cmpLabel (pc : Fin 48) : Fin 80 := ⟨pc.val,by omega⟩
def program : Program 80 := fun pc =>
  if pc.val=47 then .ret .r3
  else if h : pc.val<48 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 48 => .call 0 47 .r3
  | 50 => .field .r3 .r1 true 51
  | 51 => .branch .r3 79 70 52 79
  | 52 => .make .r2 (.pair .r0 .r1) 53
  | 53 => .field .r1 .r1 false 54
  | 54 => .field .r1 .r1 false 55
  | 55 => .call 48 56 .r3
  | 56 => .branch .r3 70 57 57 79
  | 57 => .field .r1 .r2 true 58
  | 58 => .field .r1 .r1 false 59
  | 59 => .field .r1 .r1 true 60
  | 60 => .call 48 61 .r3
  | 61 => .branch .r3 70 72 72 79
  | 70 => .make .r3 (.flag true) 71
  | 71 => .ret .r3
  | 72 => .make .r3 (.flag false) 73
  | 73 => .ret .r3
  | 78 => .call 50 79 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 80)) (source : Bits) (pc : Fin 80) : NaturalState 80 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,cmpLabel,pc.isLt,hp]

theorem run_append {s u v : NaturalState 80} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)
end DirectedFlowCutGap.KeptVertex
