import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Finite incidence packing and covering

A path is represented here by its finite, nonempty set of resources. Packing
maximizes the sum of all path amounts, subject to resource capacities. Covering
requires weight at least one on every path. These are the sum-multiflow LPs,
not maximum concurrent flow. All scalars are real with explicit nonnegativity.

The strong-duality proof uses geometric separation in finite dimensions; it
neither assumes LP duality nor asserts algorithmic or bit-complexity bounds.
-/

namespace DirectedFlowCutGap.PackingCovering

noncomputable section
open scoped BigOperators
open Set

variable {R P : Type*} [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P]

/-- The zero-one resource/path incidence matrix. -/
def incidence (resources : P → Finset R) (r : R) (p : P) : ℝ :=
  if r ∈ resources p then 1 else 0

/-- Total amount using a resource. -/
def load (resources : P → Finset R) (f : P → ℝ) (r : R) : ℝ :=
  ∑ p, incidence resources r p * f p

/-- Resource weight of a path. -/
def pathWeight (resources : P → Finset R) (w : R → ℝ) (p : P) : ℝ :=
  ∑ r, incidence resources r p * w r

/-- Total routed amount, with no prescribed amount per demand. -/
def packingValue (f : P → ℝ) : ℝ := ∑ p, f p

/-- Capacity-weighted covering objective. -/
def coveringValue (c w : R → ℝ) : ℝ := ∑ r, c r * w r

/-- Nonnegative path amounts obey every resource capacity. -/
def IsPacking (resources : P → Finset R) (c : R → ℝ) (f : P → ℝ) : Prop :=
  (∀ p, 0 ≤ f p) ∧ ∀ r, load resources f r ≤ c r

/-- Nonnegative resource weights cover every path. -/
def IsCovering (resources : P → Finset R) (w : R → ℝ) : Prop :=
  (∀ r, 0 ≤ w r) ∧ ∀ p, 1 ≤ pathWeight resources w p

omit [Fintype R] [Fintype P] [DecidableEq P] in
lemma incidence_nonneg (resources : P → Finset R) (r : R) (p : P) :
    0 ≤ incidence resources r p := by
  simp only [incidence]
  split_ifs <;> norm_num

omit [Fintype P] [DecidableEq P] in
lemma pathWeight_eq_sum (resources : P → Finset R) (w : R → ℝ) (p : P) :
    pathWeight resources w p = ∑ r ∈ resources p, w r := by
  simp [pathWeight, incidence, ite_mul]

omit [Fintype R] [DecidableEq P] in
lemma load_eq_sum_filter (resources : P → Finset R) (f : P → ℝ) (r : R) :
    load resources f r = ∑ p with r ∈ resources p, f p := by
  simp [load, incidence, ite_mul, Finset.sum_filter]

omit [Fintype R] [DecidableEq P] in
lemma load_nonneg (resources : P → Finset R) {f : P → ℝ} (hf : ∀ p, 0 ≤ f p)
    (r : R) : 0 ≤ load resources f r :=
  Finset.sum_nonneg fun p _ => mul_nonneg (incidence_nonneg resources r p) (hf p)

omit [DecidableEq P] in
lemma pairing_identity (resources : P → Finset R) (f : P → ℝ) (w : R → ℝ) :
    (∑ p, f p * pathWeight resources w p) = ∑ r, load resources f r * w r := by
  simp only [pathWeight, load, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  ring

omit [DecidableEq P] in
/-- Weak duality is finite double counting and nonnegativity. -/
theorem weak_duality (resources : P → Finset R) {c : R → ℝ} {f : P → ℝ}
    {w : R → ℝ} (hf : IsPacking resources c f) (hw : IsCovering resources w) :
    packingValue f ≤ coveringValue c w := by
  calc
    packingValue f = ∑ p, f p * 1 := by simp [packingValue]
    _ ≤ ∑ p, f p * pathWeight resources w p :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hw.2 p) (hf.1 p)
    _ = ∑ r, load resources f r * w r := pairing_identity resources f w
    _ ≤ coveringValue c w :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hf.2 r) (hw.1 r)

omit [Fintype R] [DecidableEq P] in
lemma zero_isPacking (resources : P → Finset R) {c : R → ℝ} (hc : ∀ r, 0 ≤ c r) :
    IsPacking resources c 0 := by
  constructor
  · simp
  · simpa [load] using hc

omit [Fintype P] [DecidableEq P] in
lemma one_isCovering (resources : P → Finset R)
    (hne : ∀ p, (resources p).Nonempty) : IsCovering resources 1 := by
  constructor
  · simp
  · intro p
    rw [pathWeight_eq_sum]
    simpa using (Nat.one_le_cast.mpr (Finset.card_pos.mpr (hne p)) :
      (1 : ℝ) ≤ (resources p).card)

omit [DecidableEq P] in
lemma packing_coordinate_bound (resources : P → Finset R) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, (resources p).Nonempty)
    {f : P → ℝ} (hf : IsPacking resources c f) (p : P) : f p ≤ ∑ r, c r := by
  obtain ⟨r, hr⟩ := hne p
  have hsingle : f p ≤ load resources f r := by
    have h := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset P)) =>
        mul_nonneg (incidence_nonneg resources r q) (hf.1 q)) (Finset.mem_univ p)
    simpa [incidence, hr, load] using h
  exact hsingle.trans ((hf.2 r).trans (Finset.single_le_sum (fun x _ => hc x)
    (Finset.mem_univ r)))

omit [Fintype R] [DecidableEq P] in
lemma isClosed_packings (resources : P → Finset R) (c : R → ℝ) :
    IsClosed {f | IsPacking resources c f} := by
  have hnonneg : IsClosed {f : P → ℝ | ∀ p, 0 ≤ f p} :=
    by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
  have hcap : IsClosed {f : P → ℝ | ∀ r, load resources f r ≤ c r} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro r
    apply isClosed_le _ continuous_const
    unfold load
    fun_prop
  exact hnonneg.inter hcap

omit [DecidableEq P] in
/-- Every feasible finite packing problem with nonempty paths attains its maximum. -/
theorem exists_max_packing (resources : P → Finset R) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, (resources p).Nonempty) :
    ∃ f, IsPacking resources c f ∧
      ∀ g, IsPacking resources c g → packingValue g ≤ packingValue f := by
  have hcompact : IsCompact {f | IsPacking resources c f} := by
    apply isCompact_Icc.of_isClosed_subset (isClosed_packings resources c)
    intro f hf
    exact ⟨hf.1, fun p => packing_coordinate_bound resources hc hne hf p⟩
  obtain ⟨f, hf, hmax⟩ := hcompact.exists_isMaxOn (f := packingValue)
    ⟨0, zero_isPacking resources hc⟩ (by unfold packingValue; fun_prop)
  exact ⟨f, hf, fun g hg => hmax hg⟩

omit [Fintype P] [DecidableEq P] in
/-- Clipping a covering at one preserves every path constraint. -/
lemma clip_isCovering (resources : P → Finset R) {w : R → ℝ}
    (hw : IsCovering resources w) : IsCovering resources (fun r => min (w r) 1) := by
  refine ⟨fun r => le_min (hw.1 r) zero_le_one, ?_⟩
  intro p
  rw [pathWeight_eq_sum]
  by_cases hlarge : ∃ r ∈ resources p, 1 ≤ w r
  · obtain ⟨r, hr, hwr⟩ := hlarge
    calc
      1 = min (w r) 1 := (min_eq_right hwr).symm
      _ ≤ ∑ x ∈ resources p, min (w x) 1 :=
        Finset.single_le_sum (fun x _ => le_min (hw.1 x) zero_le_one) hr
  · have heq : (∑ r ∈ resources p, min (w r) 1) = ∑ r ∈ resources p, w r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact min_eq_left (le_of_not_ge fun h => hlarge ⟨r, hr, h⟩)
    rw [heq, ← pathWeight_eq_sum]
    exact hw.2 p

omit [DecidableEq R] in
lemma clip_value_le {c w : R → ℝ} (hc : ∀ r, 0 ≤ c r) :
    coveringValue c (fun r => min (w r) 1) ≤ coveringValue c w :=
  Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hc r)

omit [Fintype P] [DecidableEq P] in
lemma isClosed_coverings (resources : P → Finset R) :
    IsClosed {w | IsCovering resources w} := by
  have hnonneg : IsClosed {w : R → ℝ | ∀ r, 0 ≤ w r} :=
    by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
  have hcover : IsClosed {w : R → ℝ | ∀ p, 1 ≤ pathWeight resources w p} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro p
    apply isClosed_le continuous_const
    unfold pathWeight
    fun_prop
  exact hnonneg.inter hcover

omit [Fintype P] [DecidableEq P] in
/-- A minimum covering exists, and one can choose all its coordinates in `[0,1]`. -/
theorem exists_min_covering (resources : P → Finset R) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, (resources p).Nonempty) :
    ∃ w, IsCovering resources w ∧ (∀ r, w r ≤ 1) ∧
      ∀ z, IsCovering resources z → coveringValue c w ≤ coveringValue c z := by
  let K : Set (R → ℝ) := {w | IsCovering resources w} ∩ Icc 0 1
  have hcompact : IsCompact K :=
    isCompact_Icc.inter_left (isClosed_coverings resources)
  have hneK : K.Nonempty := ⟨1, one_isCovering resources hne, by simp⟩
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn (f := coveringValue c) hneK
    (by unfold coveringValue; fun_prop)
  refine ⟨w, hw.1, hw.2.2, fun z hz => ?_⟩
  have hclip : (fun r => min (z r) 1) ∈ K :=
    ⟨clip_isCovering resources hz, fun r => le_min (hz.1 r) zero_le_one,
      fun r => min_le_right _ _⟩
  exact (hmin hclip).trans (clip_value_le hc)


/-- The incidence operator as a linear map. -/
def loadMap (resources : P → Finset R) : (P → ℝ) →ₗ[ℝ] (R → ℝ) where
  toFun := load resources
  map_add' f g := by
    ext r
    simp [load, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext r
    simp [load, Finset.mul_sum, mul_left_comm]

/-- Nonnegative real vectors of total mass one. -/
def unitSimplex (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1}

lemma convex_unitSimplex (I : Type*) [Fintype I] : Convex ℝ (unitSimplex I) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hf.1 i)) (mul_nonneg hb (hg.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]

lemma isCompact_unitSimplex (I : Type*) [Fintype I] : IsCompact (unitSimplex I) := by
  have hnonneg : IsClosed {z : I → ℝ | ∀ i, 0 ≤ z i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hclosed : IsClosed (unitSimplex I) :=
    hnonneg.inter (isClosed_eq (by fun_prop) continuous_const)
  apply (isCompact_Icc : IsCompact (Icc (0 : I → ℝ) 1)).of_isClosed_subset hclosed
  intro z hz
  refine ⟨hz.1, fun i => ?_⟩
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => hz.1 j)
    (Finset.mem_univ i)
  simpa [hz.2] using h

lemma single_mem_unitSimplex (I : Type*) [Fintype I] [DecidableEq I] (i : I) :
    Pi.single i (1 : ℝ) ∈ unitSimplex I := by
  refine ⟨fun j => ?_, by simp⟩
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

omit [Fintype R] in
/-- A functional bounded above on a lower orthant has nonnegative coefficients. -/
lemma nonneg_coefficients_of_bounded_orthant (F : (R → ℝ) →L[ℝ] ℝ)
    (c : R → ℝ) (u : ℝ) (h : ∀ x : R → ℝ, x ≤ c → F x < u) (r : R) :
    0 ≤ F (Pi.single r 1) := by
  by_contra! hr
  have hcu := h c le_rfl
  let a : ℝ := (u - F c + 1) / (-F (Pi.single r 1))
  have ha : 0 ≤ a := div_nonneg (by linarith) (by linarith)
  have hx : c - a • Pi.single r 1 ≤ c := by
    intro s
    apply sub_le_self
    exact mul_nonneg ha (by simp only [Pi.single_apply]; split_ifs <;> norm_num)
  have ht := h (c - a • Pi.single r 1) hx
  have heq : a * (-F (Pi.single r 1)) = u - F c + 1 :=
    div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hr))
  simp only [map_sub, map_smul, smul_eq_mul] at ht
  nlinarith

lemma functional_eq_sum (F : (R → ℝ) →L[ℝ] ℝ) (x : R → ℝ) :
    F x = ∑ r, x r * F (Pi.single r 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- If total amount `t > 0` cannot be routed, strict geometric separation
produces a feasible covering of cost strictly below `t`. This certificate
statement is the strong-duality step, and includes zero resource capacities. -/
theorem covering_certificate (resources : P → Finset R) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) {t : ℝ} (ht : 0 < t)
    (hnot : ¬ ∃ f, IsPacking resources c f ∧ packingValue f = t) :
    ∃ w, IsCovering resources w ∧ coveringValue c w < t := by
  let A : (P → ℝ) →ₗ[ℝ] (R → ℝ) := t • loadMap resources
  let K : Set (R → ℝ) := A '' unitSimplex P
  have hKconv : Convex ℝ K := (convex_unitSimplex P).linear_image A
  have hKcompact : IsCompact K :=
    (isCompact_unitSimplex P).image A.continuous_of_finiteDimensional
  have hdisj : Disjoint (Iic c) K := by
    apply Set.disjoint_left.mpr
    intro x hx hxK
    obtain ⟨z, hz, rfl⟩ := hxK
    apply hnot
    refine ⟨fun p => t * z p, ⟨fun p => mul_nonneg ht.le (hz.1 p), ?_⟩, ?_⟩
    · intro r
      have hxr := hx r
      simpa [A, loadMap, load, Finset.mul_sum, mul_left_comm] using hxr
    · simp [packingValue, ← Finset.mul_sum, hz.2]
  obtain ⟨F, u, v, hlow, huv, hhigh⟩ :=
    geometric_hahn_banach_closed_compact (convex_Iic c) isClosed_Iic
      hKconv hKcompact hdisj
  let b : R → ℝ := fun r => F (Pi.single r 1)
  have hb : ∀ r, 0 ≤ b r :=
    nonneg_coefficients_of_bounded_orthant F c u hlow
  have hFc : F c = coveringValue c b := functional_eq_sum F c
  have hFc0 : 0 ≤ F c := by
    rw [hFc]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hc r) (hb r)
  have hFcu : F c < u := hlow c (by simp)
  have hv : 0 < v := by linarith
  have hpath : ∀ p, v < t * pathWeight resources b p := by
    intro p
    have hs := hhigh (A (Pi.single p 1))
      ⟨Pi.single p 1, single_mem_unitSimplex P p, rfl⟩
    have heval : F (A (Pi.single p 1)) = t * pathWeight resources b p := by
      rw [functional_eq_sum]
      simp [A, loadMap, load, pathWeight, b, Pi.single_apply,
        ← Finset.mul_sum, mul_assoc]
    rwa [heval] at hs
  refine ⟨fun r => (t / v) * b r, ⟨fun r => mul_nonneg (div_nonneg ht.le hv.le) (hb r), ?_⟩, ?_⟩
  · intro p
    have heq : pathWeight resources (fun r => (t / v) * b r) p =
        (t * pathWeight resources b p) / v := by
      simp only [pathWeight]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [heq]
    exact (le_div_iff₀ hv).mpr (by simpa using (hpath p).le)
  · have heq : coveringValue c (fun r => (t / v) * b r) = (t * F c) / v := by
      rw [hFc]
      simp only [coveringValue]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [heq, div_lt_iff₀ hv]
    exact mul_lt_mul_of_pos_left (hFcu.trans huv) ht

/-- Attained finite packing/covering strong duality. Both optima are produced,
with all covering coordinates at most one. Empty index types and zero
capacities require no additional positivity assumptions. -/
theorem strong_duality (resources : P → Finset R) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, (resources p).Nonempty) :
    ∃ f w, IsPacking resources c f ∧ IsCovering resources w ∧
      packingValue f = coveringValue c w ∧
      (∀ g, IsPacking resources c g → packingValue g ≤ packingValue f) ∧
      (∀ z, IsCovering resources z → coveringValue c w ≤ coveringValue c z) ∧
      (∀ r, w r ≤ 1) := by
  obtain ⟨f, hf, hmax⟩ := exists_max_packing resources hc hne
  obtain ⟨w, hw, hw1, hmin⟩ := exists_min_covering resources hc hne
  refine ⟨f, w, hf, hw, ?_, hmax, hmin, hw1⟩
  apply le_antisymm (weak_duality resources hf hw)
  by_contra! hgap
  let t := (packingValue f + coveringValue c w) / 2
  have hf0 : 0 ≤ packingValue f := Finset.sum_nonneg fun p _ => hf.1 p
  have hft : packingValue f < t := by dsimp [t]; linarith
  have htw : t < coveringValue c w := by dsimp [t]; linarith
  have ht : 0 < t := lt_of_le_of_lt hf0 hft
  have hnot : ¬ ∃ g, IsPacking resources c g ∧ packingValue g = t := by
    rintro ⟨g, hg, hgt⟩
    have := hmax g hg
    rw [hgt] at this
    linarith
  obtain ⟨z, hz, hzt⟩ := covering_certificate resources hc ht hnot
  have := hmin z hz
  linarith

end
end DirectedFlowCutGap.PackingCovering
