import DirectedFlowCutGap.RetainedChargedFairBits
import DirectedFlowCutGap.BinarySamplerCost

/-!
# Charged binary sampling on the actual finite draw tree

Each finite draw uses the binary bounded-rejection computation. The
projection retains the same bit requests and legal fallback as the
existing lowered tree. The charge includes the executed binary decoder,
bound comparison and trial-counter arithmetic in its Boolean-list model.
-/

namespace DirectedFlowCutGap.BinaryDrawTreeExecution

open FiniteDrawTrees LazyFairBitTrees BinaryArithmetic
open BitSamplerCoupling

abbrev DrawTree := FiniteDrawTrees.Tree

private def bit : DrawTree Bool :=
  .draw 2 (by decide) (fun i => .pure (i.val == 1))

private theorem bitIndex_bit : BinaryRandomWord.bitIndex <$> bit = pick 2 (by decide) := by
  change FiniteDrawTrees.Tree.draw 2 (by decide) (fun i => .pure (BinaryRandomWord.bitIndex (i.val == 1))) =
    FiniteDrawTrees.Tree.draw 2 (by decide) (fun i => .pure i)
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem execute_pick_binary {A : Type} {t : DrawTree A} (h : Binary t) :
    execute (MonadicBitSampler.liftBit (m := DrawTree) (pick 2 (by decide))) t = t := by
  induction h with
  | pure a => rfl
  | @draw next _ ih =>
    simp only [execute, MonadicBitSampler.liftBit_two]
    change FiniteDrawTrees.Tree.draw 2 (by decide) (fun j => execute _ (next j)) = _
    exact congrArg (FiniteDrawTrees.Tree.draw 2 (by decide)) (funext ih)

theorem draw_observe (bound fuel : Bits) (positive : 0 < value bound) :
    BinaryBoundedSampler.observe <$> BinaryBoundedSampler.draw bit bound positive fuel =
      rejection (value bound) positive (value fuel) := by
  rw [BinaryBoundedSampler.draw_refines, bitIndex_bit, MonadicBitSampler.draw_refines]
  exact execute_pick_binary (rejection_binary ..)

private theorem ideal_bind {A B : Type} (t : DrawTree A) (f : A → DrawTree B) :
    ideal (t >>= f) = (ideal t).bind fun a => ideal (f a) :=
  law_bind _ t f

private theorem ideal_map {A B : Type} (f : A → B) (t : DrawTree A) :
    ideal (f <$> t) = (ideal t).map f :=
  law_map _ f t

private theorem word_ideal (count : Bits) :
    ideal (BinaryRandomWord.word bit count) = BinaryRandomWord.word (ideal bit) count := by
  have aux (n : ℕ) : ∀ c : Bits, value c = n →
      ideal (BinaryRandomWord.word bit c) = BinaryRandomWord.word (ideal bit) c := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      conv_lhs => rw [BinaryRandomWord.word]
      conv_rhs => rw [BinaryRandomWord.word]
      by_cases hz : (isZero c).1 = true
      · simp only [hz, dite_true]
        rfl
      · have hv : 0 < value c := Nat.pos_of_ne_zero (fun e => hz ((isZero_spec c).1.mpr e))
        have hp : value (predecessor c).1 < n := by
          rw [(predecessor_spec c).1, ← hc]
          omega
        simp only [dite_eq_right hz, ideal_bind, ih _ hp _ rfl]
        rfl
  exact aux _ count rfl

private theorem draw_ideal (bound fuel : Bits) (positive : 0 < value bound) :
    ideal (BinaryBoundedSampler.draw bit bound positive fuel) =
      BinaryBoundedSampler.draw (ideal bit) bound positive fuel := by
  have aux (n : ℕ) : ∀ f : Bits, value f = n →
      ideal (BinaryBoundedSampler.draw bit bound positive f) =
        BinaryBoundedSampler.draw (ideal bit) bound positive f := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      conv_lhs => rw [BinaryBoundedSampler.draw]
      conv_rhs => rw [BinaryBoundedSampler.draw]
      by_cases hz : (isZero f).1 = true
      · simp only [hz, dite_true]
        rfl
      · have hv : 0 < value f := Nat.pos_of_ne_zero (fun e => hz ((isZero_spec f).1.mpr e))
        have hp : value (predecessor f).1 < n := by
          rw [(predecessor_spec f).1, ← hf]
          omega
        simp only [dite_eq_right hz, ideal_bind, word_ideal]
        congr 1
        funext x
        split
        · rfl
        · rw [ideal_bind, ih _ hp _ rfl]
          rfl
  exact aux _ fuel rfl

theorem draw_cost (bound fuel : Bits) (positive : 0 < value bound)
    {r : BinaryBoundedSampler.Output bound}
    (hr : r ∈ (ideal (BinaryBoundedSampler.draw bit bound positive fuel)).support) :
    r.steps ≤ BinarySamplerCost.instructionBound bound fuel := by
  rw [draw_ideal] at hr
  exact (BinarySamplerCost.draw_bounded _ bound fuel positive hr).2.2

private theorem positive_value_bits {n : ℕ} (hn : 0 < n) : 0 < value n.bits :=
  (value_bits n).symm ▸ hn

def sample (n : ℕ) (hn : 0 < n) (T : ℕ) : DrawTree (Fin n × ℕ) :=
  (fun r => (Fin.cast (value_bits n) (BinaryBoundedSampler.observe r).value, r.steps)) <$>
    BinaryBoundedSampler.draw bit n.bits (positive_value_bits hn) T.bits

private theorem rejection_cast {a b : ℕ} (h : a = b) (ha : 0 < a) (T : ℕ) :
    (fun r => Fin.cast h (DefaultOutput.value r)) <$> rejection a ha T =
      DefaultOutput.value <$> rejection b (h ▸ ha) T := by
  subst b
  simp

theorem sample_value (n : ℕ) (hn : 0 < n) (T : ℕ) :
    Prod.fst <$> sample n hn T = DefaultOutput.value <$> rejection n hn T := by
  unfold sample
  have h := congrArg (fun t : DrawTree (DefaultOutput (value n.bits)) =>
    (fun a => Fin.cast (value_bits n) a.value) <$> t) (draw_observe n.bits T.bits (positive_value_bits hn))
  simp only [Functor.map_map] at h ⊢
  rw [h, value_bits T]
  exact rejection_cast (value_bits n) _ T

theorem sample_cost (n : ℕ) (hn : 0 < n) (T : ℕ)
    {r : Fin n × ℕ} (hr : r ∈ (ideal (sample n hn T)).support) :
    r.2 ≤ BinarySamplerCost.instructionBound n.bits T.bits := by
  unfold sample at hr
  rw [ideal_map] at hr
  obtain ⟨out, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  exact draw_cost n.bits T.bits (positive_value_bits hn) ho

def run {A : Type} (T : ℕ) : DrawTree A → DrawTree (A × ℕ)
  | .pure a => .pure (a, 0)
  | .draw n hn next => do
    let (choice, spent) ← sample n hn T
    let (out, later) ← run T (next choice)
    pure (out, spent + later)

theorem run_value {A : Type} (T : ℕ) (t : DrawTree A) : Prod.fst <$> run T t = lower T t := by
  induction t with
  | pure a => rfl
  | draw n hn next ih =>
    calc
      Prod.fst <$> run T (.draw n hn next) = sample n hn T >>= fun x =>
          Prod.fst <$> run T (next x.1) := by
        simp only [run, map_bind, Functor.map_map, bind_pure_comp]
      _ = (Prod.fst <$> sample n hn T) >>= fun x => lower T (next x) := by
        simp only [bind_map_left, ih]
      _ = lower T (.draw n hn next) := by
        rw [sample_value, bind_map_left]
        rfl

def oneDrawBound (T w : ℕ) : ℕ := 2048 * (T + 1) * (2 * T + w + 2) ^ 2

theorem sample_cost_le {n w : ℕ} (hn : 0 < n) (T : ℕ)
    (hw : FairBitWords.width n ≤ w)
    {r : Fin n × ℕ} (hr : r ∈ (ideal (sample n hn T)).support) : r.2 ≤ oneDrawBound T w := by
  have hT : T.size ≤ T := Nat.size_le.mpr T.lt_two_pow_self
  refine (sample_cost n hn T hr).trans ?_
  unfold oneDrawBound BinarySamplerCost.instructionBound
  simp only [value_bits, Nat.size_eq_bits_len, BinaryBoundedSampler.size_eq_width hn, two_mul]
  have hwidth : T + FairBitWords.width n + T.size + 2 ≤ T + T + w + 2 := by omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2)

theorem run_cost {A : Type} {t : DrawTree A} {q w : ℕ}
    (h : Within q t) (hw : WidthsLE w t) (T : ℕ)
    {r : A × ℕ} (hr : r ∈ (ideal (run T t)).support) : r.2 ≤ q * oneDrawBound T w := by
  induction h generalizing r with
  | pure q a =>
    have he : r = (a, 0) := (PMF.mem_support_pure_iff _ _).mp hr
    rw [he]
    exact Nat.zero_le _
  | @draw q n hn next kids ih =>
    cases hw with
    | draw width children =>
      simp only [run, ideal_bind] at hr
      obtain ⟨⟨j, first⟩, hj, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      obtain ⟨⟨a, later⟩, ha, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      have he : r = (a, first + later) := (PMF.mem_support_pure_iff _ _).mp hr
      have hfirst : first ≤ oneDrawBound T w := sample_cost_le hn T width hj
      have hlater : later ≤ q * oneDrawBound T w := ih j (children j) ha
      rw [he, Nat.succ_mul]
      omega

end DirectedFlowCutGap.BinaryDrawTreeExecution
