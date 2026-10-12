import DirectedFlowCutGap.SupportEdgeComparison

/-! Literal numeric tail membership and internal-mask construction. The comparison
reads padded words, and the traversal reads the retained recovered edge list. -/
namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

abbrev same := SupportRecoveryProgram.same
def member (u : Bits) : List (Bits × Bits) → Bool
  | [] => false
  | e::es => if same e.1 u then true else member u es
def memberSteps (u : Bits) : List (Bits × Bits) → ℕ
  | [] => 3
  | e::es => BinaryComparisonProgram.steps e.1 u +
    (if same e.1 u then 10 else memberSteps u es+11)
def memberCells (u : Bits) : List (Bits × Bits) → ℕ
  | [] => 1
  | e::es => BinaryComparisonProgram.cells e.1 u +
    (if same e.1 u then 1 else memberCells u es)
def bit (s t u : Bits) (es : List (Bits × Bits)) : Bool :=
  if same u s then false else if same u t then false else member u es
def mask (s t : Bits) (es : List (Bits × Bits)) (vs : List Bits) : Bits :=
  vs.map (fun u => bit s t u es)
def Context (heap : NaturalHeap) (p : ℕ) (s t : Bits) (es : List (Bits × Bits)) : Prop :=
  ∃ demand edges sr tr,heap[p]?=some (.pair demand edges) ∧
    heap[demand]?=some (.pair sr tr) ∧ BoolList heap sr s ∧ BoolList heap tr t ∧
    EdgeList heap edges es

def cmpLabel (pc : Fin 48) : Fin 160 := ⟨pc.val,by omega⟩
def program : Program 160 := fun pc =>
  if pc.val=47 then .ret .r3
  else if h : pc.val<48 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 48 => .call 0 47 .r3
  | 60 => .branch .r0 61 159 159 63
  | 61 => .make .r3 (.flag false) 62
  | 62 => .ret .r3
  | 63 => .move .r2 .r0 64
  | 64 => .field .r0 .r0 false 65
  | 65 => .field .r0 .r0 false 66
  | 66 => .call 48 67 .r3
  | 67 => .branch .r3 70 68 68 159
  | 68 => .field .r0 .r2 true 69
  | 69 => .call 60 72 .r3
  | 70 => .make .r3 (.flag true) 71
  | 71 => .ret .r3
  | 72 => .ret .r3
  | 90 => .make .r2 (.pair .r0 .r1) 91
  | 91 => .field .r1 .r1 false 92
  | 92 => .field .r1 .r1 false 93
  | 93 => .call 48 94 .r3
  | 94 => .branch .r3 110 95 95 159
  | 95 => .field .r1 .r2 true 96
  | 96 => .field .r1 .r1 false 97
  | 97 => .field .r1 .r1 true 98
  | 98 => .call 48 99 .r3
  | 99 => .branch .r3 110 100 100 159
  | 100 => .field .r0 .r2 true 101
  | 101 => .field .r0 .r0 true 102
  | 102 => .field .r1 .r2 false 103
  | 103 => .call 60 104 .r3
  | 104 => .ret .r3
  | 110 => .make .r3 (.flag false) 111
  | 111 => .ret .r3
  | 120 => .branch .r0 121 159 159 123
  | 121 => .make .r3 .nil 122
  | 122 => .ret .r3
  | 123 => .move .r2 .r0 124
  | 124 => .field .r0 .r0 true 125
  | 125 => .call 120 126 .r3
  | 126 => .make .r2 (.pair .r2 .r3) 127
  | 127 => .field .r0 .r2 false 128
  | 128 => .field .r0 .r0 false 129
  | 129 => .call 90 130 .r3
  | 130 => .field .r2 .r2 true 131
  | 131 => .make .r3 (.pair .r3 .r2) 132
  | 132 => .ret .r3
  | 150 => .call 120 151 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 160)) (source : Bits) (pc : Fin 160) : NaturalState 160 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,cmpLabel,pc.isLt,hp]

theorem run_append {s u v : NaturalState 160} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.OracleMask
