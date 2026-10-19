import LightEFTSpanners.StoredFlagBatchProbability
import LightEFTSpanners.AdaptiveVotingConcentration
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma

/-!
Unelaborated mathematical/interface draft only. Candidate coordinates are LIST
POSITIONS, including repeated keys. The source law is a literal finite product;
decoding updates the tail before the head and is empty outside visited keys.
The schedule is mathematical data, not a charged sampler or serialization.
-/
namespace LightEFTSpanners.JointFlagSampling
open Finset FiniteProbability MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Transport

theorem mass_ext {α : Type*} [Fintype α] (p q : Law α)
    (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with
  | mk pm pn pt =>
    cases q with
    | mk qm qn qt =>
      have he : pm = qm := funext h
      cases he
      rfl

theorem eq_of_prob_eq {α : Type*} [Fintype α] (p q : Law α)
    (h : ∀ P : α → Prop, p.prob P = q.prob P) : p = q := by
  classical
  apply mass_ext p q
  intro a
  simpa [Law.prob] using h (fun b => b = a)

/-- Coordinatewise pushforward of a finite independent product. -/
theorem product_map {α β I : Type*} [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] (p : Law α) (g : α → β) :
    (productLaw (J:=I) p).map (fun x i => g (x i)) =
      productLaw (J:=I) (p.map g) := by
  classical
  apply mass_ext
  intro y
  dsimp only [Law.map, Law.bind, Law.pure, productLaw]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

/-- Relate the project's measure-defined batch to literal singleton products. -/
theorem batch_eq_product {α I : Type*} [Fintype α] [Fintype I]
    [DecidableEq I] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    batchLaw (J:=I) μ = productLaw (J:=I) (Law.ofMeasure μ) := by
  unfold batchLaw productLaw Law.ofMeasure
  congr 1
  funext x
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

/-- Split an occurrence-indexed product into an independent head and tail. -/
theorem fin_cons_probability {α : Type*} [Fintype α] (p : Law α) (k : ℕ)
    (P : (Fin (k+1) → α) → Prop) :
    (productLaw (J:=Fin (k+1)) p).prob P =
      ∑ b, p.mass b * (productLaw (J:=Fin k) p).prob (fun bs => P (Fin.cons b bs)) := by
  classical
  change (∑ x : Fin (k+1) → α, if P x then ∏ i, p.mass (x i) else 0) =
    ∑ b, p.mass b * ∑ bs : Fin k → α,
      if P (Fin.cons b bs) then ∏ i, p.mass (bs i) else 0
  have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => α))
    (fun x : Fin (k+1) → α => if P x then ∏ i, p.mass (x i) else 0)
  rw [←he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ bs : Fin k → α,
      if P (Fin.cons b bs) then
        ∏ i : Fin (k+1), p.mass ((Fin.cons (α := fun _ : Fin (k+1) => α) b bs) i) else 0) =
    p.mass b * ∑ bs : Fin k → α,
      if P (Fin.cons b bs) then ∏ i, p.mass (bs i) else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bs _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases hp : P (Fin.cons b bs) <;> simp [hp]

end Transport

private theorem retainInstanceArguments {J : Type*} [Fintype J] [DecidableEq J]
    {P : Prop} (h : P) : P := h

abbrev OriginalEdge (n : ℕ) := Sym2 (Fin n)
abbrev HostFlags (n : ℕ) (J : Type*) (m : ℕ) := J → Fin m → OriginalEdge n → Bool
abbrev JointFlags (n : ℕ) (J : Type*) (m : ℕ) (l : List (OriginalEdge n)) :=
  Fin l.length → HostFlags n J m
abbrev Coordinate (n : ℕ) (J : Type*) (m : ℕ) (l : List (OriginalEdge n)) :=
  Fin l.length × (J × (Fin m × OriginalEdge n))

def candidateAt {n : ℕ} (l : List (OriginalEdge n)) (p : Fin l.length) : OriginalEdge n :=
  l[p.val]

variable {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
local instance (n : ℕ) : MeasurableSpace (Finset (OriginalEdge n)) := ⊤

/-- Tail-first occurrence order; all hosts, repetitions and original identities. -/
noncomputable def samplingSchedule (n m : ℕ) (l : List (OriginalEdge n)) :
    List (Coordinate n J m l) :=
  ((List.finRange l.length).reverse).product
    (((univ : Finset J).toList).product
      ((List.finRange m).product ((univ : Finset (OriginalEdge n)).toList)))

theorem samplingSchedule_nodup {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
    (n m : ℕ) (l : List (OriginalEdge n)) :
    (samplingSchedule (J:=J) n m l).Nodup := by
  classical
  apply @retainInstanceArguments J fintypeJ decidableEqJ
  exact List.Nodup.product (List.nodup_reverse.mpr (List.nodup_finRange _))
    (List.Nodup.product (Finset.nodup_toList _)
      (List.Nodup.product (List.nodup_finRange _) (Finset.nodup_toList _)))

theorem mem_samplingSchedule {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
    (n m : ℕ) (l : List (OriginalEdge n))
    (c : Coordinate n J m l) : c ∈ samplingSchedule (J:=J) n m l := by
  classical
  apply @retainInstanceArguments J fintypeJ decidableEqJ
  rcases c with ⟨p,j,i,d⟩
  simp [samplingSchedule, List.mem_finRange]

theorem samplingSchedule_length {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
    (n m : ℕ) (l : List (OriginalEdge n)) :
    (samplingSchedule (J:=J) n m l).length =
      l.length * Fintype.card J * m * Fintype.card (OriginalEdge n) := by
  apply @retainInstanceArguments J fintypeJ decidableEqJ
  unfold samplingSchedule
  change (((List.finRange l.length).reverse ×ˢ
      ((univ : Finset J).toList ×ˢ
        (List.finRange m ×ˢ (univ : Finset (OriginalEdge n)).toList))).length) =
    l.length * Fintype.card J * m * Fintype.card (OriginalEdge n)
  simp only [List.length_product, List.length_reverse, List.length_finRange,
    Finset.length_toList, Finset.card_univ, Nat.mul_assoc]

noncomputable def hostSourceLaw (n f m : ℕ) (hf : 0 < f) : Law (HostFlags n J m) :=
  productLaw (J:=J) (StoredFlagBatch.sourceLaw n f m hf)

noncomputable def jointSourceLaw (n f m : ℕ) (hf : 0 < f) (l : List (OriginalEdge n)) :
    Law (JointFlags n J m l) :=
  productLaw (J:=Fin l.length) (hostSourceLaw (J:=J) n f m hf)

/-- No independence/coupling assumption: the joint mass is this product. -/
theorem jointSourceLaw_mass (n f m : ℕ) (hf : 0 < f) (l : List (OriginalEdge n))
    (bits : JointFlags n J m l) :
    (jointSourceLaw n f m hf l).mass bits =
      ∏ p, ∏ j, ∏ i, ∏ d, if bits p j i d then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ)) := rfl

def decodeHost {n m : ℕ} (bits : HostFlags n J m) :
    J → Fin m → Finset (OriginalEdge n) :=
  fun j i => BernoulliFlags.selected (bits j i)

theorem decodeHost_typed {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
    {n m : ℕ} (bits : HostFlags n J m) (j : J) (i : Fin m) :
    decodeHost bits j i = StoredSample.edgeSet (StoredFlagSample.typed (bits j i)) := by
  apply @retainInstanceArguments J fintypeJ decidableEqJ
  exact (StoredFlagSample.typed_edgeSet _).symm

def decodeAssignment {n m : ℕ} :
    (l : List (OriginalEdge n)) → JointFlags n J m l → SampledGreedy.Assignment (Fin n) J m
  | [], _ => fun _ _ _ => ∅
  | e::es, bits => Function.update
      (decodeAssignment es (fun p => bits p.succ)) e (decodeHost (bits 0))

/-- This applies even when e occurs again in es: the head batch wins. -/
theorem decodeAssignment_head {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
    {n m : ℕ} (e : OriginalEdge n) (es : List (OriginalEdge n))
    (bits : JointFlags n J m (e::es)) :
    decodeAssignment (e::es) bits e = decodeHost (bits 0) := by
  apply @retainInstanceArguments J fintypeJ decidableEqJ
  simp only [decodeAssignment, Function.update_self]

theorem decodeAssignment_outside {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]
    (n m : ℕ) :
    ∀ (l : List (OriginalEdge n)) (bits : JointFlags n J m l) (e : OriginalEdge n),
      e ∉ l → decodeAssignment l bits e = (fun _ _ => ∅)
  | [], _, _, _ => by
    apply @retainInstanceArguments J fintypeJ decidableEqJ
    rfl
  | d::ds, bits, e, he => by
    apply @retainInstanceArguments J fintypeJ decidableEqJ
    have hne : e ≠ d := by
      intro h
      subst e
      exact he List.mem_cons_self
    rw [decodeAssignment, Function.update_of_ne hne]
    exact decodeAssignment_outside n m ds (fun p => bits p.succ) e
      (fun h => he (List.mem_cons_of_mem d h))

/-- Existing single-host batch theorem, made into exact finite-law equality. -/
theorem batch_decode_law (n f m : ℕ) (hf : 0 < f) :
    (StoredFlagBatch.sourceLaw n f m hf).map
        (fun bits i => BernoulliFlags.selected (bits i)) =
      drawLaw (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).toPMF.toMeasure m := by
  apply Transport.eq_of_prob_eq
  intro P
  rw [Law.prob_map]
  exact StoredFlagBatch.original_probability n f m hf P

theorem host_decode_law (n f m : ℕ) (hf : 0 < f) :
    (hostSourceLaw (J:=J) n f m hf).map decodeHost =
      SampledGreedy.freshBatchLaw (V:=Fin n) (J:=J) f hf m := by
  calc
    _ = productLaw (J:=J)
        ((StoredFlagBatch.sourceLaw n f m hf).map
          (fun bits i => BernoulliFlags.selected (bits i))) :=
      Transport.product_map _ _
    _ = productLaw (J:=J)
        (drawLaw (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).toPMF.toMeasure m) := by
      rw [batch_decode_law]
    _ = _ := by
      simpa only [SampledGreedy.freshBatchLaw, SampledGreedy.testDrawMeasure, drawLaw] using
        (Transport.batch_eq_product (I:=J)
          (drawMeasure (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).toPMF.toMeasure m)).symm

/-- Equality of every event probability, for arbitrary lists including duplicates. -/
theorem decoded_assignment_probability (n f m : ℕ) (hf : 0 < f)
    (l : List (OriginalEdge n)) (P : SampledGreedy.Assignment (Fin n) J m → Prop) :
    (jointSourceLaw (J:=J) n f m hf l).prob (fun bits => P (decodeAssignment l bits)) =
      (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m l).prob P := by
  classical
  induction l generalizing P with
  | nil =>
    simpa only [decodeAssignment, SampledGreedy.executionLaw, Law.prob_pure] using
      Law.prob_const (jointSourceLaw (J:=J) n f m hf []) (P (fun _ _ _ => ∅))
  | cons e es ih =>
    change (productLaw (J:=Fin (es.length+1)) (hostSourceLaw (J:=J) n f m hf)).prob
      (fun bits => P (Function.update (decodeAssignment es (fun p => bits p.succ)) e
        (decodeHost (bits 0)))) = _
    rw [Transport.fin_cons_probability]
    simp only [Fin.cons_zero, Fin.cons_succ]
    calc
      _ = ∑ b, (hostSourceLaw (J:=J) n f m hf).mass b *
          (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m es).prob
            (fun a => P (Function.update a e (decodeHost b))) := by
        apply Finset.sum_congr rfl
        intro b _
        exact congrArg (fun z => (hostSourceLaw (J:=J) n f m hf).mass b * z)
          (ih (fun a => P (Function.update a e (decodeHost b))))
      _ = ∑ a, (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m es).mass a *
          (hostSourceLaw (J:=J) n f m hf).prob
            (fun b => P (Function.update a e (decodeHost b))) := by
        unfold Law.prob
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        by_cases hp : P (Function.update a e (decodeHost b)) <;> simp [hp, mul_comm]
      _ = ∑ a, (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m es).mass a *
          (SampledGreedy.freshBatchLaw (V:=Fin n) (J:=J) f hf m).prob
            (fun b => P (Function.update a e b)) := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
        have hb := congrArg (fun q => q.prob (fun b => P (Function.update a e b)))
          (host_decode_law (J:=J) n f m hf)
        simpa only [Law.prob_map] using hb
      _ = _ := by
        simp only [SampledGreedy.executionLaw, Law.prob_bind, Law.prob_map]

theorem decoded_assignment_law (n f m : ℕ) (hf : 0 < f) (l : List (OriginalEdge n)) :
    (jointSourceLaw (J:=J) n f m hf l).map (decodeAssignment l) =
      SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m l := by
  apply Transport.eq_of_prob_eq
  intro P
  rw [Law.prob_map]
  exact decoded_assignment_probability n f m hf l P

end LightEFTSpanners.JointFlagSampling
