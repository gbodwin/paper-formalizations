import DirectedFlowCutGap.GuardedPackedArrayPlan
import DirectedFlowCutGap.GuardedCutoffWork

/-! Use the packed reservation trace exactly when the binary cutoff enters
the hard path. The other paths initialize a constant mask and read no tape. -/
namespace DirectedFlowCutGap.CutoffArrayStorage

open BinaryArithmetic EncodedArrayStorage Polynomial
open RetainedGridState (PairFlags Flags)
open GuardedFuelFreeRounding
open PhysicalIntegerRounding (Result)

def constantMaskCode (n : ℕ) : List (Instruction Unit) :=
  reserveArray n++List.replicate n (.store ())

theorem constant_layout (n : ℕ) :
    fresh (constantMaskCode n)=n+2 ∧ (constantMaskCode n).length=n+3 := by
  have empty (k : ℕ) : fresh (List.replicate k (Instruction.store ()))=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [List.replicate_succ,fresh,Instruction.fresh,List.map_cons,List.sum_cons,Nat.zero_add] using ih
  simp only [constantMaskCode,fresh_append,reserveArray_fresh,empty,Nat.add_zero,List.length_append,
    reserveArray_length,List.length_replicate,true_and]
  omega

def HardPlan {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L)
    (tape : Bits) (code : List (Instruction Unit)) : Prop :=
  let words := PhysicalIntegerRounding.boundaryWords n L T
  let entry := RawGraphInputStore.prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let raw := PaidTotalRawGraphExecution.run entry.1 (packed_input adj L T tape) positive
  GuardedPackedArrayPlan.ArrayPlan entry.1 n raw.1 code

private def observed {n : ℕ} (r : Result n × ℕ) : Flags n × Bits := (r.1.mask,r.1.suffix)

def Model {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) (code : List (Instruction Unit)) : Prop :=
  let gate := BinaryIntegerCutoff.compute n L
  if gate.inside && gate.hard then ∃ positive : 0<L,
    HardPlan T adj L positive tape code ∧
    (GuardedCutoffWork.runBinary T adj L tape).1.map observed=
      (hard T adj L positive tape).1.map (fun r => (r.mask,r.suffix))
  else code=constantMaskCode n ∧
    (GuardedCutoffWork.runBinary T adj L tape).1.map observed=some (Vector.replicate n gate.inside,tape)

theorem arrays : ∃ cells copies : Polynomial ℕ,
    ∀ {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits),
      ∃ code : List (Instruction Unit),
        Model T adj L tape code ∧
        fresh code ≤ cells.eval (n+T) ∧ code.length ≤ copies.eval (n+T) := by
  obtain ⟨packedCells,packedCopies,runPacked⟩ := GuardedPackedArrayPlan.hard_arrays
  refine ⟨packedCells+X+2,packedCopies+X+3,?_⟩
  intro n T adj L tape
  let gate := BinaryIntegerCutoff.compute n L
  have light : fresh (constantMaskCode n) ≤ (packedCells+X+2).eval (n+T) ∧
      (constantMaskCode n).length ≤ (packedCopies+X+3).eval (n+T) := by
    rw [(constant_layout n).1,(constant_layout n).2]
    simp only [eval_add,eval_X,eval_ofNat]
    omega
  cases inside : gate.inside with
  | false =>
    refine ⟨constantMaskCode n,?_,light⟩
    change (if gate.inside && gate.hard then _ else _)
    simp only [inside,Bool.false_and,Bool.false_eq_true,ite_false,true_and]
    simp [GuardedCutoffWork.runBinary,show (BinaryIntegerCutoff.compute n L).inside=false from inside,observed]
  | true =>
    have within : L≤n := (BinaryIntegerCutoff.inside_true n L).mp inside
    cases hard : gate.hard with
    | false =>
      refine ⟨constantMaskCode n,?_,light⟩
      change (if gate.inside && gate.hard then _ else _)
      simp only [inside,hard,Bool.true_and,Bool.false_eq_true,ite_false,true_and]
      simp [GuardedCutoffWork.runBinary,show (BinaryIntegerCutoff.compute n L).inside=true from inside,
        show (BinaryIntegerCutoff.compute n L).hard=false from hard,observed]
    | true =>
      have enough := ((BinaryIntegerCutoff.hard_true n L within).mp hard).1
      have pos : 0<L := by
        have : 0<IntegerEpochParameters.cap n := by unfold IntegerEpochParameters.cap; positivity
        omega
      obtain ⟨code,modeled,_,space,work,_⟩ := runPacked n L T adj pos tape within
      refine ⟨code,?_,?_,?_⟩
      · change (if gate.inside && gate.hard then _ else _)
        simp only [inside,hard,Bool.and_self,ite_true]
        refine ⟨pos,modeled,?_⟩
        simp [GuardedCutoffWork.runBinary,show (BinaryIntegerCutoff.compute n L).inside=true from inside,
          show (BinaryIntegerCutoff.compute n L).hard=true from hard,Function.comp_def,observed]
      · simp only [eval_add,eval_X,eval_ofNat]
        omega
      · simp only [eval_add,eval_X,eval_ofNat]
        omega

end DirectedFlowCutGap.CutoffArrayStorage
