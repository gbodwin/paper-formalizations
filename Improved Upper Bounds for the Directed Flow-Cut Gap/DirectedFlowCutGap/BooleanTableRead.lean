import DirectedFlowCutGap.ImmutableReferenceTerminal
import DirectedFlowCutGap.EncodedArrayStorage

/-!
# A closed six-instruction Boolean-table read

The input heap must already contain a Boolean list and a unary index spine.
These are representation hypotheses about actual cells, not a supplied
semantic execution or compiler-correctness premise. Building either list is
an outstanding input-representation cost. Shared immutable flag cells are
allowed. Exactly one output bit is emitted; no denoted DAG is expanded.

This proves the value of `EncodedArrayStorage.readCallback`, not its old
abstract charge 7. The concrete interpreter's own bit bound is used below.
-/
namespace DirectedFlowCutGap.BooleanTableRead
open ImmutableReferenceSimulation ImmutableReferenceTerminal

/-- Every Boolean row entry is a pair whose head is a Boolean flag cell. -/
inductive BoolList (heap : NaturalHeap) : ℕ → List Bool → Prop
  | nil {root : ℕ} : heap[root]? = some .nil → BoolList heap root []
  | cons {root head tail : ℕ} {b : Bool} {bs : List Bool} :
      heap[root]? = some (.pair head tail) → heap[head]? = some (.flag b) →
      BoolList heap tail bs → BoolList heap root (b :: bs)

/-- Only the proper-list spine is inspected; payload references are arbitrary. -/
inductive IndexSpine (heap : NaturalHeap) : ℕ → ℕ → Prop
  | nil {root : ℕ} : heap[root]? = some .nil → IndexSpine heap root 0
  | cons {root payload tail n : ℕ} : heap[root]? = some (.pair payload tail) →
      IndexSpine heap tail n → IndexSpine heap root (n+1)

/-- The instruction table is fixed independently of the heap and index. -/
def program : Program 6 := fun pc =>
  match pc.val with
  | 0 => .branch .r1 3 5 5 1
  | 1 => .field .r0 .r0 true 2
  | 2 => .field .r1 .r1 true 0
  | 3 => .field .r2 .r0 false 4
  | 4 => .emit .r2 5
  | _ => .halt

@[simp] theorem program_zero : program 0 = .branch .r1 3 5 5 1 := rfl
@[simp] theorem program_one : program 1 = .field .r0 .r0 true 2 := rfl
@[simp] theorem program_two : program 2 = .field .r1 .r1 true 0 := rfl
@[simp] theorem program_three : program 3 = .field .r2 .r0 false 4 := rfl
@[simp] theorem program_four : program 4 = .emit .r2 5 := rfl
@[simp] theorem program_five : program 5 = .halt := rfl

/-- A notation-level state constructor, not an instruction or host callback. -/
def inputState (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 6)) (source : BinaryArithmetic.Bits) (pc : Fin 6) :
    NaturalState 6 := ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

/-- Each successor consumes exactly three actual instructions and one cons
from each represented list. The zero case takes branch, field, then emit. -/
theorem read_list {heap : NaturalHeap} {n a b : ℕ} {bs : List Bool}
    (tableRep : BoolList heap a bs) (indexRep : IndexSpine heap b n)
    (legal : n < bs.length) (next c d : ℕ) (stack : List (Frame ℕ 6))
    (source : BinaryArithmetic.Bits) :
    ∃ a' b' c',
      NaturalRun program (3*n+3) (inputState heap next a b c d stack source 0)
        [.emit bs[n]] (inputState heap next a' b' c' d stack source 5) ∧
      heap[c']? = some (.flag bs[n]) := by
  induction n generalizing a b bs c with
  | zero =>
      cases tableRep with
      | nil ht => simp at legal
      | @cons a head tail bit rest ht hb hr =>
          cases indexRep with
          | nil hi =>
              refine ⟨a,b,head,?_,hb⟩
              have t0 : tickNatural program (inputState heap next a b c d stack source 0) =
                  some ⟨inputState heap next a b c d stack source 3,[],0⟩ := by
                simp [tickNatural,inputState,Registers.get,hi,tagBranch]
              have t1 : tickNatural program (inputState heap next a b c d stack source 3) =
                  some ⟨inputState heap next a b head d stack source 4,[],0⟩ := by
                simp [tickNatural,inputState,Registers.get,Registers.set,ht]
              have t2 : tickNatural program (inputState heap next a b head d stack source 4) =
                  some ⟨inputState heap next a b head d stack source 5,[.emit bit],0⟩ := by
                simp [tickNatural,inputState,Registers.get,hb]
              simpa using NaturalRun.step t0 (NaturalRun.step t1
                (NaturalRun.step t2 (NaturalRun.done _)))
  | succ n ih =>
      cases tableRep with
      | nil ht => simp at legal
      | @cons a head tail bit rest ht hb hr =>
          cases indexRep with
          | @cons b payload cursor n hi hiTail =>
              have hn : n < rest.length := by simpa using legal
              obtain ⟨a',b',c',run,flag⟩ := ih hr hiTail hn c
              refine ⟨a',b',c',?_,flag⟩
              have t0 : tickNatural program (inputState heap next a b c d stack source 0) =
                  some ⟨inputState heap next a b c d stack source 1,[],0⟩ := by
                simp [tickNatural,inputState,Registers.get,hi,tagBranch]
              have t1 : tickNatural program (inputState heap next a b c d stack source 1) =
                  some ⟨inputState heap next tail b c d stack source 2,[],0⟩ := by
                simp [tickNatural,inputState,Registers.get,Registers.set,ht]
              have t2 : tickNatural program (inputState heap next tail b c d stack source 2) =
                  some ⟨inputState heap next tail cursor c d stack source 0,[],0⟩ := by
                simp [tickNatural,inputState,Registers.get,Registers.set,hi]
              have count : 3*(n+1)+3 = ((3*n+3)+1)+1+1 := by omega
              rw [count]
              simpa using NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2 run))

/-- Frame, heap, allocation cursor, source, and scratch register are unchanged.
The final result register names the selected flag and PC 5 is the actual halt. -/
theorem read_table_high {m : ℕ} (table : Vector Bool m) (i : Fin m)
    (initial : NaturalState 6) (pc0 : initial.pc = 0)
    (tableRep : BoolList initial.heap initial.registers.a table.toList)
    (indexRep : IndexSpine initial.heap initial.registers.b i.val) :
    ∃ final, NaturalRun program (3*i.val+3) initial [.emit table[i.val]] final ∧
      final.heap = initial.heap ∧ final.next = initial.next ∧
      final.stack = initial.stack ∧ final.source = initial.source ∧
      final.registers.d = initial.registers.d ∧ final.pc = 5 ∧
      final.heap[final.registers.c]? = some (.flag table[i.val]) ∧
      tickNatural program final = none ∧
      (EncodedArrayStorage.readCallback table i).1 = table[i.val] := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 tableRep indexRep
          subst pc
          have legal : i.val < table.toList.length := by simpa only [Vector.length_toList] using i.isLt
          obtain ⟨a',b',c',run,flag⟩ :=
            read_list tableRep indexRep legal next c d stack source
          refine ⟨inputState heap next a' b' c' d stack source 5,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,rfl⟩
          · simpa only [inputState,Vector.getElem_toList] using run
          · simpa only [inputState,Vector.getElem_toList] using flag
          · simp [tickNatural,inputState]

/-- The existing lower interpreter realizes this concrete read with exactly
its emitted bit and source, and its own physical bit-operation bound. -/
theorem read_table_bit {m H B : ℕ} (table : Vector Bool m) (i : Fin m)
    (initial : BitState 6) (bounded : initial.Bounded H B)
    (pc0 : initial.pc = 0)
    (tableRep : BoolList (eraseState initial).heap (eraseState initial).registers.a table.toList)
    (indexRep : IndexSpine (eraseState initial).heap (eraseState initial).registers.b i.val) :
    ∃ q out, Run program (3*i.val+3) q initial [.emit table[i.val]] out ∧
      out.Bounded (H+(3*i.val+3)) (B+(3*i.val+3)) ∧
      q ≤ runBound 6 H B (3*i.val+3) ∧ out.source = initial.source ∧
      out.pc = 5 ∧
      (eraseState out).heap[(eraseState out).registers.c]? = some (.flag table[i.val]) ∧
      (attempt program out).result = none ∧
      q+(attempt program out).operations ≤ completeBound 6 H B (3*i.val+3) := by
  obtain ⟨final,high,hh,hn,hstack,hsource,hscratch,hpc,hflag,hhalt,hvalue⟩ :=
    read_table_high table i (eraseState initial) pc0 tableRep indexRep
  obtain ⟨q,out,run,erase,bound,cost,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,hhalt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨q,out,run,bound,cost,source.trans hsource,?_,?_,stop,?_⟩
  · exact (congrArg State.pc erase).trans hpc
  · rw [erase]; exact hflag
  · exact (terminal_accounting run bounded stop).2

end DirectedFlowCutGap.BooleanTableRead
