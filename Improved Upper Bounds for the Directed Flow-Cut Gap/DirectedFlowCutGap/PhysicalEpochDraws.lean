import DirectedFlowCutGap.PhysicalDrawSequenceProgram
import DirectedFlowCutGap.RetainedDrawTrees

/-!
# The draw sequence for one retained rounding epoch

The encoded bounds are the decreasing permutation bounds followed by
one grid bound per active demand. The checked physical batch interprets
the same ordered calls as the established fair-tape tree. The mask
filter, construction of the bound table, and use of the resulting
permutation and grid indices are separate steps.
-/

namespace DirectedFlowCutGap.PhysicalEpochDraws

open BinaryArithmetic FiniteDrawTrees
open PhysicalBoundedDrawProgram (outcome)
open PhysicalDrawSequenceProgram (batch)
open PhysicalBoundedDrawExecution (draw sample checkedFrom)
open EncodedSolverBits (Tape)

abbrev Positive := {n : ℕ // 0<n}

def permutationBounds : ℕ → List Positive
  | 0 => []
  | m+1 => ⟨m+1,Nat.zero_lt_succ m⟩::permutationBounds m

def cellBounds (L : ℕ) (positive : 0<L) (m : ℕ) : List Positive :=
  List.replicate m ⟨L,positive⟩

def epochBounds (L : ℕ) (positive : 0<L) (m : ℕ) : List Bits :=
  (permutationBounds m++cellBounds L positive m).map fun k => k.val.bits

def permutationValues : (m : ℕ) → FinitePermutationSampler.Tape m → List ℕ
  | 0,_ => []
  | m+1,(i,is) => i.val::permutationValues m is

def cellValues (L : ℕ) : (m : ℕ) → FiniteGridSampler.Cells L m → List ℕ
  | 0,_ => []
  | m+1,(i,is) => i.val::cellValues L m is

def values (L m : ℕ) (t : FinitePermutationSampler.Tape m × FiniteGridSampler.Cells L m) : List ℕ :=
  permutationValues m t.1 ++ cellValues L m t.2

section Calls

variable {f : Type → Type} [Monad f] [LawfulMonad f]
variable (pull : (n : ℕ) → 0<n → f (Fin n))

def calls : List Positive → f (List ℕ)
  | [] => pure []
  | x::xs => do
    let i ← pull x.val x.property
    List.cons i.val <$> calls xs

theorem permutation_calls (m : ℕ) :
    permutationValues m <$> execute pull (RetainedDrawTrees.permutation m) =
      calls pull (permutationBounds m) := by
  induction m with
  | zero =>
    change ((fun _ : Unit => ([] : List ℕ)) <$> (pure () : f Unit)) = pure []
    exact LawfulMonad.map_pure'
  | succ m ih =>
    simp only [RetainedDrawTrees.permutation,MonadicBitSampler.execute_bind,MonadicBitSampler.execute_pick,
      ← bind_pure_comp,bind_assoc,calls,permutationBounds]
    congr 1
    funext i
    change (do
      let a ← execute pull (map (fun t : FinitePermutationSampler.Tape m => (i,t))
        (RetainedDrawTrees.permutation m))
      pure (a.1.val::permutationValues m a.2)) = _
    rw [MonadicBitSampler.execute_map]
    simp only [bind_pure_comp]
    have h := congrArg (Functor.map (List.cons i.val)) ih
    simpa only [Functor.map_map,Function.comp_def] using h

theorem cell_calls (L : ℕ) (positive : 0<L) (m : ℕ) :
    cellValues L m <$> execute pull (RetainedDrawTrees.cells L positive m) =
      calls pull (cellBounds L positive m) := by
  induction m with
  | zero =>
    change ((fun _ : Unit => ([] : List ℕ)) <$> (pure () : f Unit)) = pure []
    exact LawfulMonad.map_pure'
  | succ m ih =>
    simp only [RetainedDrawTrees.cells,MonadicBitSampler.execute_bind,MonadicBitSampler.execute_pick,
      ← bind_pure_comp,bind_assoc,
      cellBounds,List.replicate_succ,calls]
    congr 1
    funext i
    change (do
      let a ← execute pull (map (fun t : FiniteGridSampler.Cells L m => (i,t))
        (RetainedDrawTrees.cells L positive m))
      pure (a.1.val::cellValues L m a.2)) = _
    rw [MonadicBitSampler.execute_map]
    simp only [bind_pure_comp]
    have h := congrArg (Functor.map (List.cons i.val)) ih
    simpa only [Functor.map_map,Function.comp_def,cellBounds] using h

theorem calls_append (a b : List Positive) :
    calls pull (a++b) = (do let xs ← calls pull a; (xs++·) <$> calls pull b) := by
  induction a with
  | nil => simp [calls]
  | cons x xs ih =>
    simp only [List.cons_append,calls,ih,← bind_pure_comp,bind_assoc,pure_bind]

theorem epoch_calls (L : ℕ) (positive : 0<L) (m : ℕ) :
    values L m <$> execute pull (RetainedDrawTrees.tape L positive m) =
      calls pull (permutationBounds m++cellBounds L positive m) := by
  rw [calls_append,← permutation_calls,← cell_calls]
  simp only [RetainedDrawTrees.tape,MonadicBitSampler.execute_bind,MonadicBitSampler.execute_map,
    ← bind_pure_comp,bind_assoc,pure_bind,values]

end Calls

def checkedValues (fuel : ℕ) (bounds : List Bits) (tape : Bits) (start : ℕ) :
    Option (List ℕ × Tape) :=
  let out := batch fuel bounds tape
  if out.requests.length ≤ tape.length then
    some (out.draws.map (fun r => value r.index),(out.suffix,start+out.requests.length))
  else none

private theorem cast_draw (fuel n m : ℕ) (hn : 0 < n) (hm : 0 < m) (h : n=m) (tape : Tape) :
    (fun p => (p.1.value,p.2)) <$> (draw fuel m hm).run tape =
      (fun p => (Fin.cast h p.1.value,p.2)) <$> (draw fuel n hn).run tape := by
  subst m
  rfl

theorem calls_run (fuel : ℕ) (bounds : List Positive) (tape : Bits) (start : ℕ) :
    (calls (sample fuel) bounds).run (tape,start) =
      checkedValues fuel (bounds.map fun k => k.val.bits) tape start := by
  induction bounds generalizing tape start with
  | nil => simp [calls,StateT.run_pure,checkedValues,batch]
  | cons x xs ih =>
    let bound := x.val.bits
    have hnum : value bound=x.val := value_bits _
    have positive : 0<value bound := hnum.symm ▸ x.property
    have width : bound.length=FairBitWords.width (value bound) := by
      rw [hnum]
      exact (Nat.size_eq_bits_len x.val).trans (BinaryBoundedSampler.size_eq_width x.property)
    have trace := PhysicalBoundedDrawExecution.draw_run bound fuel positive width tape start
    let hd := outcome bound fuel tape
    let bs := xs.map fun k => k.val.bits
    let tl := batch fuel bs hd.suffix
    simp only [calls,StateT.run_bind,StateT.run_map,List.map_cons,sample]
    rw [cast_draw fuel (value bound) x.val positive x.property hnum,trace]
    change ((checkedFrom bound fuel positive tape start).map _).bind _ = _
    unfold checkedFrom checkedValues
    change ((if hd.requests.length ≤ tape.length then
        some (PhysicalBoundedDrawExecution.observe bound fuel tape positive,(hd.suffix,start+hd.requests.length))
      else none).map _).bind _ =
      if (hd.requests++tl.requests).length ≤ tape.length then
        some (value hd.index :: tl.draws.map (fun r => value r.index),
          (tl.suffix,start+(hd.requests++tl.requests).length))
      else none
    by_cases enough : hd.requests.length ≤ tape.length
    · rw [ite_eq_left enough]
      simp only [Option.map_some,Option.bind_some,Fin.val_cast,PhysicalBoundedDrawExecution.observe]
      rw [ih hd.suffix (start+hd.requests.length)]
      have tailLength : hd.suffix.length = tape.length-hd.requests.length := by
        have eq : hd.suffix=tape.drop hd.requests.length :=
          (PhysicalBoundedDrawProgram.exact_requests bound fuel tape).2.1
        rw [eq,List.length_drop]
      have guard : (hd.requests++tl.requests).length ≤ tape.length ↔ tl.requests.length ≤ hd.suffix.length := by
        rw [List.length_append,tailLength]
        omega
      simp only [checkedValues,guard]
      change Option.map (fun p : List ℕ × Tape => (value hd.index::p.1,p.2))
        (if tl.requests.length ≤ hd.suffix.length then
          some (tl.draws.map (fun r => value r.index),(tl.suffix,start+hd.requests.length+tl.requests.length))
        else none) = _
      split <;> simp_all [List.length_append,Nat.add_assoc]
    · rw [ite_eq_right enough]
      have guard : ¬ (hd.requests++tl.requests).length ≤ tape.length := by
        simp only [List.length_append]
        omega
      rw [ite_eq_right guard]
      rfl

theorem epoch_run (T L m : ℕ) (positive : 0<L) (tape : Bits) :
    (EncodedSolverBits.run (LazyFairBitTrees.lower T (RetainedDrawTrees.tape L positive m)) tape).map
        (fun p => (values L m p.1,p.2)) =
      checkedValues T (epochBounds L positive m) tape 0 := by
  rw [PhysicalBoundedDrawExecution.solver_run]
  change ((fun p => (values L m p.1,p.2)) <$>
     (execute (sample T) (RetainedDrawTrees.tape L positive m)).run (tape,0)) = _
  rw [← StateT.run_map,epoch_calls]
  exact calls_run T (permutationBounds m++cellBounds L positive m) tape 0

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

theorem physical_epoch {H A W fuel L m : ℕ} (positive : 0<L) (initial : BitState 94)
    (bounded : initial.Bounded H A) (hp : initial.pc=14) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (words : PathCostMaterialization.WordList (eraseState initial).heap (eraseState initial).registers.a
      (epochBounds L positive m))
    (trials : IndexSpine (eraseState initial).heap (eraseState initial).registers.b fuel)
    (widths : ∀ x ∈ epochBounds L positive m,x.length ≤ W) :
    let caps := epochBounds L positive m
    let observed := batch fuel caps initial.source
    let budget := PhysicalDrawSequenceProgram.instructionBound W fuel caps.length
    let run := GuardedReferenceExecution.execute PhysicalDrawSequenceProgram.program (budget+1) initial 0
    match (EncodedSolverBits.run (LazyFairBitTrees.lower fuel (RetainedDrawTrees.tape L positive m))
      initial.source).map (fun p => (values L m p.1,p.2)) with
    | none => run=none
    | some (indices,(rest,reads)) =>
      ∃ out charge, run=some (out,charge) ∧
        PhysicalDrawSequenceProgram.StoredBatch (eraseState out).heap (eraseState out).registers.d observed.draws ∧
        indices=observed.draws.map (fun r => value r.index) ∧ reads=observed.requests.length ∧
        out.source=rest ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=15 ∧
        (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
        charge ≤ completeBound 94 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 94 := by
  dsimp only
  rw [epoch_run]
  have result := PhysicalDrawSequenceProgram.guarded_batch initial bounded hp hc hn words trials widths
  unfold checkedValues
  by_cases enough : (batch fuel (epochBounds L positive m) initial.source).requests.length ≤ initial.source.length
  · simp only [enough,ite_true,Nat.zero_add] at result ⊢
    obtain ⟨out,charge,hr,rep,source,stack,pc,ext,cost⟩ := result
    exact ⟨out,charge,hr,rep,True.intro,True.intro,source,stack,pc,ext,cost⟩
  · simp only [enough,ite_false] at result ⊢
    exact result

end DirectedFlowCutGap.PhysicalEpochDraws
