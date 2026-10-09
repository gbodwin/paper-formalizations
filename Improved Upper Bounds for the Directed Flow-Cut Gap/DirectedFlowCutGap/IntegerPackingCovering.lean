import DirectedFlowCutGap.PackingCovering

/-!
# Finite natural-incidence packing and covering

This extends the proved geometric-separation argument to a natural-valued
resource incidence matrix. In particular, a joint path profile consumes the
SUM of the resource incidences of its paths: repeated resource use is counted
with its full multiplicity, never collapsed into a set. Each column must have
a positive entry for finite attained strong duality. Empty column types and
zero capacities are allowed. No linear-programming duality is assumed.
-/

namespace DirectedFlowCutGap.IntegerPackingCovering

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Set

variable {R P : Type*} [Fintype R] [Fintype P] 

/-- Total amount using a resource. -/
def load (incidence : R → P → ℕ) (f : P → ℝ) (r : R) : ℝ :=
  ∑ p, (incidence r p : ℝ) * f p

/-- Resource weight of a path. -/
def pathWeight (incidence : R → P → ℕ) (w : R → ℝ) (p : P) : ℝ :=
  ∑ r, (incidence r p : ℝ) * w r

/-- Total routed amount, with no prescribed amount per demand. -/
def packingValue (f : P → ℝ) : ℝ := ∑ p, f p

/-- Capacity-weighted covering objective. -/
def coveringValue (c w : R → ℝ) : ℝ := ∑ r, c r * w r

/-- Nonnegative path amounts obey every resource capacity. -/
def IsPacking (incidence : R → P → ℕ) (c : R → ℝ) (f : P → ℝ) : Prop :=
  (∀ p, 0 ≤ f p) ∧ ∀ r, load incidence f r ≤ c r

/-- Nonnegative resource weights cover every path. -/
def IsCovering (incidence : R → P → ℕ) (w : R → ℝ) : Prop :=
  (∀ r, 0 ≤ w r) ∧ ∀ p, 1 ≤ pathWeight incidence w p

omit [Fintype R] in
lemma load_nonneg (incidence : R → P → ℕ) {f : P → ℝ} (hf : ∀ p, 0 ≤ f p)
    (r : R) : 0 ≤ load incidence f r :=
  Finset.sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (hf p)

lemma pairing_identity (incidence : R → P → ℕ) (f : P → ℝ) (w : R → ℝ) :
    (∑ p, f p * pathWeight incidence w p) = ∑ r, load incidence f r * w r := by
  simp only [pathWeight, load, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Weak duality is finite double counting and nonnegativity. -/
theorem weak_duality (incidence : R → P → ℕ) {c : R → ℝ} {f : P → ℝ}
    {w : R → ℝ} (hf : IsPacking incidence c f) (hw : IsCovering incidence w) :
    packingValue f ≤ coveringValue c w := by
  calc
    packingValue f = ∑ p, f p * 1 := by simp [packingValue]
    _ ≤ ∑ p, f p * pathWeight incidence w p :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hw.2 p) (hf.1 p)
    _ = ∑ r, load incidence f r * w r := pairing_identity incidence f w
    _ ≤ coveringValue c w :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hf.2 r) (hw.1 r)

omit [Fintype R] in
lemma zero_isPacking (incidence : R → P → ℕ) {c : R → ℝ} (hc : ∀ r, 0 ≤ c r) :
    IsPacking incidence c 0 := by
  constructor
  · simp
  · simpa [load] using hc

omit [Fintype P] in
lemma one_isCovering (incidence : R → P → ℕ)
    (hne : ∀ p, ∃ r, 0 < incidence r p) : IsCovering incidence 1 := by
  constructor
  · simp
  · intro p
    obtain ⟨r, hr⟩ := hne p
    have hpos : (1 : ℝ) ≤ incidence r p := by exact_mod_cast (Nat.succ_le_iff.mpr hr)
    exact hpos.trans (by
      simpa [pathWeight] using (Finset.single_le_sum
        (fun x (_ : x ∈ (Finset.univ : Finset R)) => Nat.cast_nonneg (incidence x p))
        (Finset.mem_univ r)))

lemma packing_coordinate_bound (incidence : R → P → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, ∃ r, 0 < incidence r p)
    {f : P → ℝ} (hf : IsPacking incidence c f) (p : P) : f p ≤ ∑ r, c r := by
  obtain ⟨r, hr⟩ := hne p
  have hsingle : f p ≤ load incidence f r := by
    have h := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset P)) =>
        mul_nonneg (Nat.cast_nonneg (incidence r q)) (hf.1 q)) (Finset.mem_univ p)
    have hpos : (1 : ℝ) ≤ incidence r p := by exact_mod_cast (Nat.succ_le_iff.mpr hr)
    calc
      f p = 1 * f p := by ring
      _ ≤ (incidence r p : ℝ) * f p := mul_le_mul_of_nonneg_right hpos (hf.1 p)
      _ ≤ load incidence f r := h
  exact hsingle.trans ((hf.2 r).trans (Finset.single_le_sum (fun x _ => hc x)
    (Finset.mem_univ r)))

omit [Fintype R] in
lemma isClosed_packings (incidence : R → P → ℕ) (c : R → ℝ) :
    IsClosed {f | IsPacking incidence c f} := by
  have hnonneg : IsClosed {f : P → ℝ | ∀ p, 0 ≤ f p} :=
    by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
  have hcap : IsClosed {f : P → ℝ | ∀ r, load incidence f r ≤ c r} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro r
    apply isClosed_le _ continuous_const
    unfold load
    fun_prop
  exact hnonneg.inter hcap

/-- Every feasible finite packing problem with positive-incidence columns attains its maximum. -/
theorem exists_max_packing (incidence : R → P → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, ∃ r, 0 < incidence r p) :
    ∃ f, IsPacking incidence c f ∧
      ∀ g, IsPacking incidence c g → packingValue g ≤ packingValue f := by
  have hcompact : IsCompact {f | IsPacking incidence c f} := by
    apply isCompact_Icc.of_isClosed_subset (isClosed_packings incidence c)
    intro f hf
    exact ⟨hf.1, fun p => packing_coordinate_bound incidence hc hne hf p⟩
  obtain ⟨f, hf, hmax⟩ := hcompact.exists_isMaxOn (f := packingValue)
    ⟨0, zero_isPacking incidence hc⟩ (by unfold packingValue; fun_prop)
  exact ⟨f, hf, fun g hg => hmax hg⟩

omit [Fintype P] in
/-- Clipping a covering at one preserves every path constraint. -/
lemma clip_isCovering (incidence : R → P → ℕ) {w : R → ℝ}
    (hw : IsCovering incidence w) : IsCovering incidence (fun r => min (w r) 1) := by
  refine ⟨fun r => le_min (hw.1 r) zero_le_one, ?_⟩
  intro p
  by_cases hlarge : ∃ r, 0 < incidence r p ∧ 1 ≤ w r
  · obtain ⟨r, hr, hwr⟩ := hlarge
    have hpos : (1 : ℝ) ≤ incidence r p := by exact_mod_cast (Nat.succ_le_iff.mpr hr)
    calc
      1 ≤ (incidence r p : ℝ) * min (w r) 1 := by simpa [min_eq_right hwr]
      _ ≤ pathWeight incidence (fun r => min (w r) 1) p :=
        Finset.single_le_sum
          (fun x _ => mul_nonneg (Nat.cast_nonneg (incidence x p)) (le_min (hw.1 x) zero_le_one))
          (Finset.mem_univ r)
  · have heq : pathWeight incidence (fun r => min (w r) 1) p =
        pathWeight incidence w p := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : incidence r p = 0
      · simp [hr]
      · have hwr : w r ≤ 1 := le_of_not_ge fun h =>
          hlarge ⟨r, Nat.pos_of_ne_zero hr, h⟩
        simp only [min_eq_left hwr]
    rw [heq]
    exact hw.2 p

lemma clip_value_le {c w : R → ℝ} (hc : ∀ r, 0 ≤ c r) :
    coveringValue c (fun r => min (w r) 1) ≤ coveringValue c w :=
  Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hc r)

omit [Fintype P] in
lemma isClosed_coverings (incidence : R → P → ℕ) :
    IsClosed {w | IsCovering incidence w} := by
  have hnonneg : IsClosed {w : R → ℝ | ∀ r, 0 ≤ w r} :=
    by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
  have hcover : IsClosed {w : R → ℝ | ∀ p, 1 ≤ pathWeight incidence w p} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro p
    apply isClosed_le continuous_const
    unfold pathWeight
    fun_prop
  exact hnonneg.inter hcover

omit [Fintype P] in
/-- A minimum covering exists, and one can choose all its coordinates in `[0,1]`. -/
theorem exists_min_covering (incidence : R → P → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, ∃ r, 0 < incidence r p) :
    ∃ w, IsCovering incidence w ∧ (∀ r, w r ≤ 1) ∧
      ∀ z, IsCovering incidence z → coveringValue c w ≤ coveringValue c z := by
  let K : Set (R → ℝ) := {w | IsCovering incidence w} ∩ Icc 0 1
  have hcompact : IsCompact K :=
    isCompact_Icc.inter_left (isClosed_coverings incidence)
  have hneK : K.Nonempty := ⟨1, one_isCovering incidence hne, by simp⟩
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn (f := coveringValue c) hneK
    (by unfold coveringValue; fun_prop)
  refine ⟨w, hw.1, hw.2.2, fun z hz => ?_⟩
  have hclip : (fun r => min (z r) 1) ∈ K :=
    ⟨clip_isCovering incidence hz, fun r => le_min (hz.1 r) zero_le_one,
      fun r => min_le_right _ _⟩
  exact (hmin hclip).trans (clip_value_le hc)


/-- The incidence operator as a linear map. -/
def loadMap (incidence : R → P → ℕ) : (P → ℝ) →ₗ[ℝ] (R → ℝ) where
  toFun := load incidence
  map_add' f g := by
    ext r
    simp [load, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext r
    simp [load, Finset.mul_sum, mul_left_comm]

open PackingCovering (unitSimplex convex_unitSimplex isCompact_unitSimplex
  single_mem_unitSimplex nonneg_coefficients_of_bounded_orthant functional_eq_sum)

/-- If total amount `t > 0` cannot be routed, strict geometric separation
produces a feasible covering of cost strictly below `t`. This certificate
statement is the strong-duality step, and includes zero resource capacities. -/
theorem covering_certificate (incidence : R → P → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) {t : ℝ} (ht : 0 < t)
    (hnot : ¬ ∃ f, IsPacking incidence c f ∧ packingValue f = t) :
    ∃ w, IsCovering incidence w ∧ coveringValue c w < t := by
  classical
  let A : (P → ℝ) →ₗ[ℝ] (R → ℝ) := t • loadMap incidence
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
  have hpath : ∀ p, v < t * pathWeight incidence b p := by
    intro p
    have hs := hhigh (A (Pi.single p 1))
      ⟨Pi.single p 1, single_mem_unitSimplex P p, rfl⟩
    have heval : F (A (Pi.single p 1)) = t * pathWeight incidence b p := by
      rw [functional_eq_sum]
      simp [A, loadMap, load, pathWeight, b, Pi.single_apply,
        ← Finset.mul_sum, mul_assoc]
    rwa [heval] at hs
  refine ⟨fun r => (t / v) * b r, ⟨fun r => mul_nonneg (div_nonneg ht.le hv.le) (hb r), ?_⟩, ?_⟩
  · intro p
    have heq : pathWeight incidence (fun r => (t / v) * b r) p =
        (t * pathWeight incidence b p) / v := by
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
theorem strong_duality (incidence : R → P → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (hne : ∀ p, ∃ r, 0 < incidence r p) :
    ∃ f w, IsPacking incidence c f ∧ IsCovering incidence w ∧
      packingValue f = coveringValue c w ∧
      (∀ g, IsPacking incidence c g → packingValue g ≤ packingValue f) ∧
      (∀ z, IsCovering incidence z → coveringValue c w ≤ coveringValue c z) ∧
      (∀ r, w r ≤ 1) := by
  obtain ⟨f, hf, hmax⟩ := exists_max_packing incidence hc hne
  obtain ⟨w, hw, hw1, hmin⟩ := exists_min_covering incidence hc hne
  refine ⟨f, w, hf, hw, ?_, hmax, hmin, hw1⟩
  apply le_antisymm (weak_duality incidence hf hw)
  by_contra! hgap
  let t := (packingValue f + coveringValue c w) / 2
  have hf0 : 0 ≤ packingValue f := Finset.sum_nonneg fun p _ => hf.1 p
  have hft : packingValue f < t := by dsimp [t]; linarith
  have htw : t < coveringValue c w := by dsimp [t]; linarith
  have ht : 0 < t := lt_of_le_of_lt hf0 hft
  have hnot : ¬ ∃ g, IsPacking incidence c g ∧ packingValue g = t := by
    rintro ⟨g, hg, hgt⟩
    have := hmax g hg
    rw [hgt] at this
    linarith
  obtain ⟨z, hz, hzt⟩ := covering_certificate incidence hc ht hnot
  have := hmin z hz
  linarith

end
end DirectedFlowCutGap.IntegerPackingCovering
