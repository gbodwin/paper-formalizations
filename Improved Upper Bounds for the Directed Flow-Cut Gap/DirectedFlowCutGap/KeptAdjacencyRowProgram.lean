import DirectedFlowCutGap.ActualKeptMaskInput

namespace DirectedFlowCutGap.KeptAdjacencyRow
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def Context (heap : NaturalHeap) (p : ℕ) (keep : Bool) (kept : Bits) : Prop :=
  ∃ k mask,heap[p]?=some (.pair k mask) ∧ heap[k]?=some (.flag keep) ∧ BoolList heap mask kept

theorem context_extend {heap : NaturalHeap} {p : ℕ} {keep : Bool} {kept : Bits}
    (h : Context heap p keep kept) (extra : NaturalHeap) : Context (heap++extra) p keep kept := by
  obtain ⟨k,m,hp,hk,hm⟩ := h
  exact ⟨k,m,lookup_extend hp extra,lookup_extend hk extra,boolList_extend hm extra⟩

def row (keep : Bool) : Bits → Bits → Bits
  | a::as,k::ks => (a && keep && k)::row keep as ks
  | _,_ => []

def steps (keep : Bool) : Bits → Bits → ℕ
  | a::as,_k::ks => (if a then if keep then 24 else 21 else 19)+steps keep as ks
  | _,_ => 3

def program : Program 36 := fun pc => match pc.val with
  | 0 => .branch .r0 1 35 35 3
  | 1 => .make .r3 .nil 2
  | 2 => .ret .r3
  | 3 => .make .r2 (.pair .r0 .r1) 4
  | 4 => .field .r3 .r0 false 5
  | 5 => .branch .r3 35 16 6 35
  | 6 => .field .r3 .r1 false 7
  | 7 => .branch .r3 35 16 8 35
  | 8 => .field .r3 .r1 true 9
  | 9 => .field .r3 .r3 false 10
  | 10 => .branch .r3 35 16 14 35
  | 14 => .make .r3 (.flag true) 17
  | 16 => .make .r3 (.flag false) 17
  | 17 => .make .r2 (.pair .r2 .r3) 18
  | 18 => .field .r0 .r2 false 19
  | 19 => .field .r0 .r0 false 20
  | 20 => .field .r0 .r0 true 21
  | 21 => .field .r1 .r2 false 22
  | 22 => .field .r1 .r1 true 23
  | 23 => .field .r3 .r1 true 24
  | 24 => .field .r3 .r3 true 25
  | 25 => .field .r1 .r1 false 26
  | 26 => .make .r1 (.pair .r1 .r3) 27
  | 27 => .call 0 28 .r3
  | 28 => .field .r2 .r2 true 29
  | 29 => .make .r3 (.pair .r2 .r3) 30
  | 30 => .ret .r3
  | 34 => .call 0 35 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 36)) (source : Bits) (pc : Fin 36) : NaturalState 36 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem run_append {s u v : NaturalState 36} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)
end DirectedFlowCutGap.KeptAdjacencyRow
