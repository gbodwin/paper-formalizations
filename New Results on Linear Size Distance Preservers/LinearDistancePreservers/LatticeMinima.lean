import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

namespace LinearDistancePreservers.LatticeMinima
open Set Submodule Module Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- A discrete full lattice has an actual shortest vector outside every
proper real subspace. This is an attained minimum, not an infimum assumption. -/
theorem exists_shortest_outside (hspan : Submodule.span ℝ (L : Set E) = ⊤)
    (S : Submodule ℝ E) (hS : S ≠ ⊤) :
    ∃ v ∈ L, v ∉ S ∧ ∀ z ∈ L, z ∉ S → ‖v‖ ≤ ‖z‖ := by
  have hex : ∃ z ∈ L, z ∉ S := by
    by_contra! h
    have he : Submodule.span ℝ (L : Set E) ≤ S := Submodule.span_le.mpr h
    rw [hspan] at he
    exact hS (top_le_iff.mp he)
  obtain ⟨z,hz,hzS⟩ := hex
  have hclosed : IsClosed (L : Set E) := by
    change IsClosed (L.toAddSubgroup : Set E)
    exact AddSubgroup.isClosed_of_discreteTopology
  have hfinite : Set.Finite ((closedBall (0 : E) ‖z‖ ∩ L) \ S) :=
    (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      isBounded_closedBall hclosed).sdiff
  have hzne : z ∈ (closedBall (0 : E) ‖z‖ ∩ L) \ S := ⟨⟨by simp,hz⟩,hzS⟩
  obtain ⟨v,hv,hmin⟩ := Set.exists_min_image _ (fun x : E => ‖x‖) hfinite ⟨z,hzne⟩
  refine ⟨v,hv.1.2,hv.2,?_⟩
  intro w hw hwS
  by_cases hnorm : ‖w‖ ≤ ‖z‖
  · exact hmin w ⟨⟨by simpa using hnorm,hw⟩,hwS⟩
  · exact (hmin z hzne).trans (le_of_not_ge hnorm)

/-- An independent family realizing the successive minima, with the full
short-vector span property. No reduction or transference certificate is supplied. -/
theorem exists_minima_family (hspan : Submodule.span ℝ (L : Set E) = ⊤)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∃ v : Fin k → E, LinearIndependent ℝ v ∧ (∀ i, v i ∈ L) ∧
      ∀ i, ∀ z ∈ L, ‖z‖ < ‖v i‖ → z ∈ Submodule.span ℝ (v '' Set.Iio i) := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0,linearIndependent_empty_type,?_,?_⟩ <;> intro i <;> exact i.elim0
  | succ k ih =>
    obtain ⟨v,hv,hvL,hsmall⟩ := ih (by omega)
    have hS : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
      intro he
      have hd := finrank_span_eq_card hv
      rw [he,finrank_top,Fintype.card_fin] at hd
      omega
    obtain ⟨w,hwL,hwS,hmin⟩ := exists_shortest_outside L hspan _ hS
    refine ⟨Fin.snoc v w,linearIndependent_finSnoc.mpr ⟨hv,hwS⟩,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hwL
      · simpa using hvL j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro z hz hnorm
        have hzS : z ∈ Submodule.span ℝ (Set.range v) := by
          by_contra hn
          have := hmin z hz hn
          simp only [Fin.snoc_last] at hnorm
          linarith
        apply Submodule.span_mono (s := Set.range v) (t := Fin.snoc v w '' Set.Iio (Fin.last k)) _ hzS
        rintro _ ⟨j,rfl⟩
        exact ⟨j.castSucc,by simp,by simp⟩
      · intro z hz hnorm
        simp only [Fin.snoc_castSucc] at hnorm
        apply Submodule.span_mono (s := v '' Set.Iio j)
          (t := Fin.snoc v w '' Set.Iio j.castSucc) _ (hsmall j z hz hnorm)
        rintro _ ⟨l,hl,rfl⟩
        exact ⟨l.castSucc,by simpa using hl,by simp⟩

/-- A full real basis of lattice vectors attaining all successive minima.
It need not generate the lattice over ℤ; that stronger property is not claimed. -/
theorem exists_minima_basis (hspan : Submodule.span ℝ (L : Set E) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E,
      (∀ i, b i ∈ L) ∧
      (∀ i, ∀ z ∈ L, ‖z‖ < ‖b i‖ → z ∈ Submodule.span ℝ (b '' Set.Iio i)) := by
  obtain ⟨v,hv,hvL,hsmall⟩ := exists_minima_family L hspan (Module.finrank ℝ E) le_rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv (by simp),?_,?_⟩
  · simpa using hvL
  · simpa using hsmall

/-- The attained minima are ordered by the greedy flag. -/
theorem minima_norm_monotone {d : ℕ} (b : Basis (Fin d) ℝ E)
    (hL : ∀ i, b i ∈ L)
    (hsmall : ∀ i, ∀ z ∈ L, ‖z‖ < ‖b i‖ → z ∈ Submodule.span ℝ (b '' Set.Iio i)) :
    Monotone (fun i => ‖b i‖) := by
  intro i j hij
  by_contra! h
  exact b.linearIndependent.notMem_span_image (by simpa using not_lt_of_ge hij)
    (hsmall i (b j) (hL j) h)

/-- Rounding in any real lattice-vector basis supplies an actual lattice
point, even when the basis spans only a finite-index sublattice over ℤ. -/
theorem exists_near_lattice {d : ℕ} (b : Basis (Fin d) ℝ E)
    (hL : ∀ i, b i ∈ L) (x : E) :
    ∃ z ∈ L, dist x z ≤ ∑ i, ‖b i‖ := by
  have hspan : Submodule.span ℤ (Set.range b) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hL i
  refine ⟨ZSpan.floor b x,hspan (ZSpan.floor b x).property,?_⟩
  simpa only [dist_eq_norm,ZSpan.fract] using ZSpan.norm_fract_le b x

section InnerProduct
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]

/-- Gram--Schmidt supplies orthonormal coordinates adapted to the attained
minima flag. A nonzero i-th coordinate of a lattice vector certifies its
norm is at least the i-th minimum. -/
theorem exists_minima_coordinates {d : ℕ} (L : Submodule ℤ F)
    (b : Basis (Fin d) ℝ F)
    (hsmall : ∀ i, ∀ z ∈ L, ‖z‖ < ‖b i‖ → z ∈ Submodule.span ℝ (b '' Set.Iio i)) :
    ∃ e : OrthonormalBasis (Fin d) ℝ F,
      ∀ i, ∀ z ∈ L, e.repr z i ≠ 0 → ‖b i‖ ≤ ‖z‖ := by
  let e := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  refine ⟨e,?_⟩
  intro i z hz hcoord
  by_contra! hnorm
  have hker : Submodule.span ℝ (b '' Set.Iio i) ≤ (e.toBasis.coord i).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change e.toBasis.repr (b j) i = 0
    rw [e.coe_toBasis_repr_apply]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' _ _ hj
  have hh := hker (hsmall i z hz hnorm)
  change e.toBasis.repr z i = 0 at hh
  rw [e.coe_toBasis_repr_apply] at hh
  exact hcoord hh

/-- The orthogonal open box at the successive-minimum scales contains no
nonzero lattice vector. This is the geometric input to Minkowski's volume
argument for a dimension-dependent transference constant. -/
theorem minima_box_lattice_free {d : ℕ} (hd : 0 < d) (L : Submodule ℤ F)
    (b : Basis (Fin d) ℝ F) (e : OrthonormalBasis (Fin d) ℝ F)
    (hmono : Monotone (fun i => ‖b i‖))
    (hcoord : ∀ i, ∀ z ∈ L, e.repr z i ≠ 0 → ‖b i‖ ≤ ‖z‖)
    {z : F} (hz : z ∈ L) (hbox : ∀ i, |e.repr z i| < ‖b i‖ / (d : ℝ)) : z = 0 := by
  classical
  by_contra hne
  have hex : ∃ i, e.repr z i ≠ 0 := by
    by_contra! hh
    apply hne
    apply e.repr.injective
    ext i
    simpa using hh i
  let I := Finset.univ.filter (fun i => e.repr z i ≠ 0)
  have hI : I.Nonempty := by obtain ⟨i,hi⟩ := hex; exact ⟨i,by simp [I,hi]⟩
  let i := I.max' hI
  have hi : e.repr z i ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem I hI)).2
  have hmin := hcoord i z hz hi
  have hbi : 0 < ‖b i‖ := norm_pos_iff.mpr (b.ne_zero i)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by positivity
  have hbound (j : Fin d) : |e.repr z j| < ‖b i‖ / (d : ℝ) := by
    by_cases hj : e.repr z j = 0
    · rw [hj,abs_zero]; positivity
    · have hji : j ≤ i := Finset.le_max' I _ (by simp [I,hj])
      exact (hbox j).trans_le (div_le_div_of_nonneg_right (hmono hji) hdp.le)
  have hsq (j : Fin d) : (e.repr z j)^2 < (‖b i‖ / (d : ℝ))^2 := by
    have hh := hbound j
    have := abs_nonneg (e.repr z j)
    have := sq_abs (e.repr z j)
    nlinarith
  have hsum : ∑ j, (e.repr z j)^2 < (d : ℝ)*(‖b i‖ / (d : ℝ))^2 := by
    calc
      _ < ∑ _j : Fin d, (‖b i‖ / (d : ℝ))^2 :=
        Finset.sum_lt_sum (fun j _ => (hsq j).le) ⟨i,Finset.mem_univ i,hsq i⟩
      _ = _ := by simp
  have he : ‖z‖^2 = ∑ j, (e.repr z j)^2 := by
    rw [← EuclideanSpace.real_norm_sq_eq,e.repr.norm_map]
  have hden : (d : ℝ)*(‖b i‖ / (d : ℝ))^2 ≤ ‖b i‖^2 := by
    have hh := mul_le_mul_of_nonneg_right (show (d : ℝ) ≤ (d : ℝ)^2 by nlinarith)
      (sq_nonneg (‖b i‖ / (d : ℝ)))
    have he' : (d : ℝ)^2*(‖b i‖ / (d : ℝ))^2 = ‖b i‖^2 := by field_simp
    rwa [he'] at hh
  rw [← he] at hsum
  nlinarith [norm_nonneg z]

variable [MeasurableSpace F] [BorelSpace F]
open MeasureTheory

/-- A dimension-dependent upper product bound for the actual successive
minima, derived from Minkowski's first theorem and the empty orthogonal box. -/
theorem minima_product_le {d : ℕ} (hd : 0 < d) (L : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin d) ℝ F) (e : OrthonormalBasis (Fin d) ℝ F)
    (hmono : Monotone (fun i => ‖b i‖))
    (hcoord : ∀ i, ∀ z ∈ L, e.repr z i ≠ 0 → ‖b i‖ ≤ ‖z‖) :
    (∏ i, ‖b i‖) ≤ (d : ℝ)^d * ZLattice.covolume L := by
  classical
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  let r : Fin d → ℝ := fun i => ‖b i‖ / d
  have hr (i : Fin d) : 0 < r i := div_pos (norm_pos_iff.mpr (b.ne_zero i)) hdp
  let S : Set F := {z | ∀ i, |e.repr z i| < r i}
  let T : Set (Fin d → ℝ) := Set.pi Set.univ (fun i => Set.Ioo (-r i) (r i))
  let f : F → Fin d → ℝ := fun z i => e.repr z i
  have hST : S = f ⁻¹' T := by ext z; simp [S,T,f,abs_lt]
  have hT : MeasurableSet T := MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioo)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
  have hvol : volume.real S = (2 / (d : ℝ))^d * ∏ i, ‖b i‖ := by
    rw [hST,hf.measureReal_preimage hT.nullMeasurableSet]
    change (volume T).toReal = _
    rw [volume_pi_pi,ENNReal.toReal_prod]
    have he : (∏ i, (volume (Set.Ioo (-r i) (r i))).toReal) = ∏ i, ((2 / (d : ℝ))*‖b i‖) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.volume_Ioo,ENNReal.toReal_ofReal (by have := hr i; linarith)]
      dsimp [r]
      ring
    rw [he,Finset.prod_mul_distrib]
    simp [div_pow]
  have hconv : Convex ℝ S := by
    rw [hST]
    exact (convex_pi (fun _ _ => convex_Ioo _ _)).linear_preimage e.toBasis.equivFun.toLinearMap
  have hsymm : ∀ z ∈ S, -z ∈ S := by
    intro z hz i
    simpa using hz i
  let bZ := Module.Free.chooseBasis ℤ L
  let F₀ := ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)
  have hfund : IsAddFundamentalDomain L F₀ volume := ZLattice.isAddFundamentalDomain bZ volume
  have hdim : Module.finrank ℝ F = d := by simpa using Module.finrank_eq_card_basis b
  have hmeasure : volume S ≤ volume F₀ * 2^(Module.finrank ℝ F) := by
    by_contra! hv
    letI : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
    have hf' : IsAddFundamentalDomain L.toAddSubgroup F₀ volume := hfund
    obtain ⟨z,hne,hz⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hf' hsymm hconv hv
    apply hne
    apply Subtype.ext
    exact minima_box_lattice_free hd L b e hmono hcoord z.property hz
  have hfinite : volume F₀ ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (bZ.ofZLatticeBasis ℝ)).measure_lt_top.ne
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hfinite (by simp)) hmeasure
  change volume.real S ≤ (volume F₀ * 2^(Module.finrank ℝ F)).toReal at hreal
  rw [hvol,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,hdim] at hreal
  change (2 / (d : ℝ))^d * ∏ i, ‖b i‖ ≤ volume.real F₀ * 2^d at hreal
  rw [← ZLattice.covolume_eq_measure_fundamentalDomain L volume hfund] at hreal
  have hh := mul_le_mul_of_nonneg_left hreal (pow_nonneg (show 0 ≤ (d : ℝ)/2 by positivity) d)
  have hcancel : ((d : ℝ)/2)^d*(2/(d : ℝ))^d = 1 := by
    rw [← mul_pow]
    have he : (d : ℝ)/2*(2/(d : ℝ)) = 1 := by field_simp
    rw [he,one_pow]
  have hcoef : ((d : ℝ)/2)^d*2^d = (d : ℝ)^d := by rw [← mul_pow]; congr 1; ring
  calc
    _ = ((d : ℝ)/2)^d * ((2/(d : ℝ))^d * ∏ i, ‖b i‖) := by rw [← mul_assoc,hcancel,one_mul]
    _ ≤ _ := hh
    _ = (((d : ℝ)/2)^d*2^d) * ZLattice.covolume L := by ring
    _ = _ := by rw [hcoef]

end InnerProduct
end LinearDistancePreservers.LatticeMinima
