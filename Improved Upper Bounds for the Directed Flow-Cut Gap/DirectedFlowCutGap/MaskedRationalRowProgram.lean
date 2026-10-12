import DirectedFlowCutGap.CanonicalRationalSum

/-! A literal aligned mask/row scan. False entries allocate the original zero
fraction; they remain in the list and are not silently dropped from the sum. -/
namespace DirectedFlowCutGap.MaskedRationalRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def program : Program 24 := fun pc => match pc.val with
  | 0 => .branch .r0 1 23 23 3
  | 1 => .make .r3 .nil 2
  | 2 => .ret .r3
  | 3 => .make .r2 (.pair .r0 .r1) 4
  | 4 => .field .r0 .r0 true 5
  | 5 => .field .r1 .r1 true 6
  | 6 => .call 0 7 .r3
  | 7 => .make .r2 (.pair .r2 .r3) 8
  | 8 => .field .r0 .r2 false 9
  | 9 => .field .r1 .r0 true 10
  | 10 => .field .r1 .r1 false 11
  | 11 => .branch .r1 23 12 16 23
  | 12 => .make .r0 .nil 13
  | 13 => .make .r1 (.flag true) 14
  | 14 => .make .r1 (.pair .r1 .r0) 15
  | 15 => .make .r0 (.pair .r0 .r1) 19
  | 16 => .field .r0 .r0 false 17
  | 17 => .field .r0 .r0 false 19
  | 19 => .field .r3 .r2 true 20
  | 20 => .make .r3 (.pair .r0 .r3) 21
  | 21 => .ret .r3
  | 22 => .call 0 23 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 24)) (source : Bits) (pc : Fin 24) : NaturalState 24 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
def result (xs : List Fraction) (mask : List Bool) : List Fraction :=
  List.zipWith (fun x enabled => if enabled then x else BinaryRational.zero) xs mask
def steps : List Bool → ℕ
  | [] => 3
  | enabled::bs => steps bs+(if enabled then 15 else 17)
def cells : List Bool → ℕ
  | [] => 1
  | enabled::bs => cells bs+(if enabled then 3 else 7)

theorem run_append {s u v : NaturalState 24} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem cons_return {heap : NaturalHeap} {next a b c d savedRoot tail : ℕ} {x : Fraction} {xs : List Fraction}
    (hpair : heap[c]?=some (.pair savedRoot tail)) (hx : Stored heap a x)
    (ht : StoredList heap tail xs) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 24) (stack : List (Frame ℕ 24)) (source : Bits) :
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 19) []
      (state (heap++[.pair a tail]) (next+1) saved.a saved.b saved.c next stack source pc) ∧
    StoredList (heap++[.pair a tail]) next (x::xs) := by
  have t19 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 19)=
      some ⟨state heap next a b c tail (⟨pc,.r3,saved⟩::stack) source 20,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hpair]
  have t20 : tickNatural program (state heap next a b c tail (⟨pc,.r3,saved⟩::stack) source 20)=
      some ⟨state (heap++[.pair a tail]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 21,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t21 : tickNatural program (state (heap++[.pair a tail]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 21)=
      some ⟨state (heap++[.pair a tail]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨.step t19 (.step t20 (.step t21 (.done _))),
    .cons (by simp [hn]) (stored_extend hx _) (list_extend ht _)⟩
end DirectedFlowCutGap.MaskedRationalRow
