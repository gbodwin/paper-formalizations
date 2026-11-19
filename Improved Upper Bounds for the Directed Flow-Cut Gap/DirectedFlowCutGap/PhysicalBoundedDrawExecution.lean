import DirectedFlowCutGap.PhysicalBoundedDrawProgram
import DirectedFlowCutGap.EncodedSolverBits
import DirectedFlowCutGap.GuardedReferenceExecution

/-!
# Exact tape semantics of the physical draw

Check the full request record against the available tape. The projection
returns no result on a missing bit, even though the raw reference machine
fills an empty request with false. On success it matches the established
bounded rejection tree, including the default flag and both counters.
-/

namespace DirectedFlowCutGap.PhysicalBoundedDrawExecution

open BinaryArithmetic PhysicalBoundedDrawProgram PhysicalFairWordProgram
open EncodedSolverBits (Tape)

private def bitValue (b : Bool) : Fin 2 := if b then 1 else 0

private def bit : StateT Tape Option (Fin 2) :=
  fun (bits,reads) =>
    match bits with
    | [] => none
    | b::rest => some (bitValue b,(rest,reads+1))

private def read (n : ℕ) (_ : 0<n) : StateT Tape Option (Fin n) :=
  fun (bits,reads) =>
    match bits with
    | [] => none
    | b::rest => if h : n=2 then some (h.symm ▸ bitValue b,(rest,reads+1)) else none

private theorem binary_execute {A : Type} {tree : FiniteDrawTrees.Tree A} (h : LazyFairBitTrees.Binary tree) :
    FiniteDrawTrees.execute read tree = FiniteDrawTrees.execute (MonadicBitSampler.liftBit bit) tree := by
  induction h with
  | pure => rfl
  | draw h ih =>
    simp only [FiniteDrawTrees.execute,MonadicBitSampler.liftBit_two,ih]
    rfl

private theorem digits_lt (w : ℕ) (tape : Bits) : value (digits w tape)<2^w := by
  simpa only [digits_length] using value_lt (digits w tape)

private theorem word_from (w : ℕ) (tape : Bits) (readCount : ℕ) :
    (MonadicBitSampler.wordValue bit w).run (tape,readCount) =
      if w ≤ tape.length then
        some ((⟨value (digits w tape),digits_lt w tape⟩ : Fin (2^w)),(tape.drop w,readCount+w))
      else none := by
  induction w generalizing tape readCount with
  | zero => simp [MonadicBitSampler.wordValue,StateT.run_pure,digits,value]
  | succ w ih =>
    cases tape with
    | nil =>
      have hb : bit.run ([],readCount)=none := rfl
      simp [MonadicBitSampler.wordValue,StateT.run_bind,hb]
    | cons b bs =>
      have hb : bit.run (b::bs,readCount)=some (bitValue b,(bs,readCount+1)) := rfl
      simp only [MonadicBitSampler.wordValue,StateT.run_bind,StateT.run_pure,hb,
        List.length_cons,Nat.succ_le_succ_iff,List.drop_succ_cons]
      change ((MonadicBitSampler.wordValue bit w).run (bs,readCount+1)).bind _ = _
      rw [ih]
      split
      · cases b <;> simp [bitValue,digits,value,Nat.add_comm,Nat.add_left_comm]
      · rfl

def observe (bound : Bits) (fuel : ℕ) (tape : Bits) (positive : 0<value bound) :
    BitSamplerCoupling.DefaultOutput (value bound) :=
  let out := outcome bound fuel tape
  ⟨⟨value out.index,index_lt bound fuel tape positive⟩,out.failed,
    out.requests.length / bound.length,out.requests.length⟩

def checkedFrom (bound : Bits) (fuel : ℕ) (positive : 0<value bound) (tape : Bits) (start : ℕ) :
    Option (BitSamplerCoupling.DefaultOutput (value bound) × Tape) :=
  let out := outcome bound fuel tape
  if out.requests.length ≤ tape.length then
    some (observe bound fuel tape positive,(out.suffix,start+out.requests.length))
  else none

theorem checked_run (bound : Bits) (fuel : ℕ) (positive : 0<value bound)
    (width : bound.length=FairBitWords.width (value bound)) (tape : Bits) (start : ℕ) :
    (MonadicBitSampler.draw bit (value bound) positive fuel).run (tape,start) =
      checkedFrom bound fuel positive tape start := by
  induction fuel generalizing tape start with
  | zero =>
    simp [MonadicBitSampler.draw,StateT.run_pure,checkedFrom,observe,outcome,value]
  | succ fuel ih =>
    simp only [MonadicBitSampler.draw,StateT.run_bind]
    rw [word_from,← width]
    let x := digits bound.length tape
    let rest := tape.drop bound.length
    have wpos : 0<bound.length := width.symm ▸ FairBitWords.width_pos (value bound)
    by_cases enough : bound.length ≤ tape.length
    · simp only [enough,ite_true]
      change ((if h : value x < value bound then
        pure ⟨⟨value x,h⟩,false,1,bound.length⟩
      else do
        let result ← MonadicBitSampler.draw bit (value bound) positive fuel
        pure ⟨result.value,result.failed,result.trials+1,bound.length+result.bits⟩
        ) : StateT Tape Option (BitSamplerCoupling.DefaultOutput (value bound))).run
          (rest,start+bound.length) = _
      by_cases h : value x < value bound
      · have noReject : (lessEqual bound x).1 = false := by
          cases hc : (lessEqual bound x).1
          · rfl
          · exact (Nat.not_le_of_lt h ((lessEqual_spec _ _).1.mp hc)).elim
        have hr : (lessEqual bound (digits bound.length tape)).1 = false := noReject
        simp [h,checkedFrom,observe,outcome,hr,digits_length,enough,Nat.div_self wpos,rest,x]
      · have reject : (lessEqual bound (digits bound.length tape)).1=true :=
          (lessEqual_spec _ _).1.mpr (Nat.le_of_not_gt h)
        simp only [h,dite_false,StateT.run_bind,StateT.run_pure]
        rw [ih]
        let next := outcome bound fuel rest
        have hguard : bound.length+next.requests.length ≤ tape.length ↔ next.requests.length ≤ rest.length := by
          simp only [rest,List.length_drop]
          omega
        change ((checkedFrom bound fuel positive rest (start+bound.length)).bind _) = _
        have hnext : (outcome bound (fuel+1) tape) = {next with requests := x++next.requests} := by
          simp only [outcome,reject,ite_true]
          rfl
        unfold checkedFrom
        rw [hnext]
        simp only [List.length_append,digits_length,x,hguard]
        by_cases hv : next.requests.length ≤ rest.length
        · simp [hv,observe,hnext,x,next,digits_length,Nat.add_div_left _ wpos,Nat.add_assoc]
        · simp [hv,next]
    · simp only [enough,ite_false]
      change none = checkedFrom bound (fuel+1) positive tape start
      have hneeds : bound.length ≤ (outcome bound (fuel+1) tape).requests.length := by
        simp only [outcome]
        split <;> simp [digits_length]
      simp only [checkedFrom,show ¬ (outcome bound (fuel+1) tape).requests.length ≤ tape.length from
        fun h => enough (hneeds.trans h),ite_false]

theorem run_rejection (bound : Bits) (fuel : ℕ) (positive : 0<value bound)
    (width : bound.length=FairBitWords.width (value bound)) (tape : Bits) :
    EncodedSolverBits.run (LazyFairBitTrees.rejection (value bound) positive fuel) tape =
      checkedFrom bound fuel positive tape 0 := by
  unfold EncodedSolverBits.run
  change (FiniteDrawTrees.execute read (LazyFairBitTrees.rejection (value bound) positive fuel)).run (tape,0) = _
  rw [binary_execute (LazyFairBitTrees.rejection_binary _ _ _),← MonadicBitSampler.draw_refines]
  exact checked_run bound fuel positive width tape 0

def draw (fuel n : ℕ) (positive : 0<n) : StateT Tape Option (BitSamplerCoupling.DefaultOutput n) :=
  MonadicBitSampler.draw bit n positive fuel

theorem draw_run (bound : Bits) (fuel : ℕ) (positive : 0<value bound)
    (width : bound.length=FairBitWords.width (value bound)) (tape : Bits) (start : ℕ) :
    (draw fuel (value bound) positive).run (tape,start) = checkedFrom bound fuel positive tape start :=
  checked_run bound fuel positive width tape start

def sample (fuel n : ℕ) (positive : 0<n) : StateT Tape Option (Fin n) :=
  (fun r => r.value) <$> draw fuel n positive

theorem solver_run {A : Type} (fuel : ℕ) (tree : FiniteDrawTrees.Tree A) (tape : Bits) :
    EncodedSolverBits.run (LazyFairBitTrees.lower fuel tree) tape =
      (FiniteDrawTrees.execute (sample fuel) tree).run (tape,0) := by
  unfold EncodedSolverBits.run
  change (FiniteDrawTrees.execute read (LazyFairBitTrees.lower fuel tree)).run (tape,0) = _
  rw [binary_execute (LazyFairBitTrees.lower_binary fuel tree),MonadicBitSampler.execute_lower_refines]
  have h : MonadicBitSampler.sample bit fuel = sample fuel := by
    funext n positive
    simp only [MonadicBitSampler.sample,sample,draw,bind_pure_comp]
  rw [h]

open BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal

def ObservedAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (r : BitSamplerCoupling.DefaultOutput n) : Prop :=
  ∃ word flag digits, heap[root]?=some (.pair word flag) ∧ BoolList heap word digits ∧
    heap[flag]?=some (.flag r.failed) ∧ value digits=r.value.val

theorem guarded_draw {H A fuel : ℕ} {bound : Bits} (initial : BitState 78)
    (bounded : initial.Bounded H A) (hp : initial.pc=18) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (hb : BoolList (eraseState initial).heap (eraseState initial).registers.a bound)
    (hf : IndexSpine (eraseState initial).heap (eraseState initial).registers.b fuel)
    (positive : 0<value bound) (width : bound.length=FairBitWords.width (value bound)) :
    let budget := instructionBound bound.length fuel
    let execution := GuardedReferenceExecution.execute PhysicalBoundedDrawProgram.program (budget+1) initial 0
    match EncodedSolverBits.run (LazyFairBitTrees.rejection (value bound) positive fuel) initial.source with
    | none => execution=none
    | some (expected,(remaining,_)) =>
      ∃ out charge, execution=some (out,charge) ∧
        ObservedAt (eraseState out).heap (eraseState out).registers.d expected ∧
        out.source=remaining ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=19 ∧
        (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
        charge ≤ completeBound 78 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 78 := by
  let budget := instructionBound bound.length fuel
  let v := outcome bound fuel initial.source
  let k := instructions bound fuel initial.source+1
  obtain ⟨q,out,hr,hrep,hsource,hstack,hpc,he,hstop,hcost⟩ := physical_draw initial bounded hp hc hn hb hf
  have hsteps : k ≤ budget := instructions_le bound fuel initial.source
  have guard := GuardedReferenceExecution.execute_eq hr hstop (budget+1) 0 (by omega)
  rw [GuardedReferenceExecution.count_reads] at guard
  dsimp only
  rw [run_rejection bound fuel positive width]
  unfold checkedFrom
  by_cases enough : v.requests.length ≤ initial.source.length
  · simp only [show (outcome bound fuel initial.source).requests.length ≤ initial.source.length from enough,ite_true] at guard ⊢
    refine ⟨out,_,guard,?_,hsource,hstack,hpc,he,?_⟩
    · obtain ⟨w,f,hpair,hw,hf⟩ := hrep
      exact ⟨w,f,v.index,hpair,hw,hf,rfl⟩
    · have extra := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 78)
        (Nat.add_le_add_right hsteps 1)
      simpa only [Nat.zero_add] using Nat.add_le_add hcost extra
  · simp only [show ¬ (outcome bound fuel initial.source).requests.length ≤ initial.source.length from enough,ite_false] at guard ⊢
    exact guard

end DirectedFlowCutGap.PhysicalBoundedDrawExecution
