import LinearDistancePreservers.LatticeDual
import LinearDistancePreservers.LatticeBody
import LinearDistancePreservers.LatticeCapWidth
import Mathlib.Tactic.Module
import Mathlib.Analysis.Real.Sqrt


namespace LinearDistancePreservers.LatticeMinima
open Module Set Metric
open scoped RealInnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L]

/-- An empty affine ellipsoid gives a nonzero integral direction of bounded
width on every fixed dilation of that ellipsoid. The linear change of
coordinates is arbitrary; no lattice basis or flatness certificate is supplied. -/
theorem exists_width_of_empty_ellipsoid {n : ℕ} (hdim : Module.finrank ℝ F = n+1)
    (T : F ≃L[ℝ] F) (c : F) {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (hempty : ∀ z ∈ L, r ≤ ‖T.symm (z-c)‖) :
    ∃ q : F, q ≠ 0 ∧ (∀ z ∈ L, ∃ k : ℤ, inner ℝ q z = (k : ℝ)) ∧
      ∀ x y : F, ‖T.symm (x-c)‖ ≤ A → ‖T.symm (y-c)‖ ≤ A →
        inner ℝ q x-inner ℝ q y ≤ 2*A*((n+1 : ℕ) : ℝ)^(n+2)/r := by
  let L' := ZLattice.comap ℝ L T.toLinearMap
  have hfree : ∀ z ∈ L', r ≤ dist (T.symm c) z := by
    intro z hz
    have hh := hempty (T z) hz
    simpa [map_sub,dist_eq_norm,norm_sub_rev] using hh
  obtain ⟨q',hq',hq'int,hq'norm⟩ := exists_short_dual_of_empty_ball L' hdim (T.symm c) hr hfree
  let f : F →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ F q').comp T.symm.toContinuousLinearMap
  let q := (InnerProductSpace.toDual ℝ F).symm f
  have hq (x : F) : inner ℝ q x = inner ℝ q' (T.symm x) := by
    change inner ℝ ((InnerProductSpace.toDual ℝ F).symm f) x = _
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  have hqn : q ≠ 0 := by
    intro heq
    have hh := hq (T q')
    simp only [heq,inner_zero_left,T.symm_apply_apply] at hh
    exact hq' (inner_self_eq_zero.mp hh.symm)
  refine ⟨q,hqn,?_,?_⟩
  · intro z hz
    rw [hq]
    apply hq'int
    change T (T.symm z) ∈ L
    simpa using hz
  · intro x y hx hy
    rw [hq,hq,← inner_sub_right]
    have he : T.symm x-T.symm y = T.symm (x-c)-T.symm (y-c) := by
      simp only [map_sub]; abel
    rw [he]
    have hb : ‖T.symm (x-c)-T.symm (y-c)‖ ≤ 2*A := by
      calc
        _ ≤ ‖T.symm (x-c)‖+‖T.symm (y-c)‖ := norm_sub_le _ _
        _ ≤ 2*A := by linarith
    calc
      _ ≤ ‖q'‖*‖T.symm (x-c)-T.symm (y-c)‖ := real_inner_le_norm _ _
      _ ≤ (((n+1 : ℕ) : ℝ)^(n+2)/r)*(2*A) :=
        mul_le_mul hq'norm hb (norm_nonneg _) (by positivity)
      _ = _ := by ring

end LinearDistancePreservers.LatticeMinima

namespace LinearDistancePreservers.LatticeMinima
open scoped RealInnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]

/-- Axial and transverse dilation, expressed without choosing coordinates. -/
noncomputable def stretch (u : F) (a b : ℝ) : F →L[ℝ] F :=
  b • ContinuousLinearMap.id ℝ F +
    (a-b) • (InnerProductSpace.toDual ℝ F u).smulRight u

theorem stretch_apply (u x : F) (a b : ℝ) :
    stretch u a b x = b • x + ((a-b)*inner ℝ u x) • u := by
  simp [stretch,smul_smul]

theorem inner_stretch (u x : F) (a b : ℝ) (hu : ‖u‖ = 1) :
    inner ℝ u (stretch u a b x) = a*inner ℝ u x := by
  rw [stretch_apply,inner_add_right,inner_smul_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
  ring

theorem stretch_stretch (u x : F) {a b : ℝ} (hu : ‖u‖ = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    stretch u a⁻¹ b⁻¹ (stretch u a b x) = x := by
  rw [stretch_apply,inner_stretch u x a b hu,stretch_apply]
  simp only [smul_add,smul_smul]
  have he : b⁻¹*((a-b)*inner ℝ u x)+(a⁻¹-b⁻¹)*(a*inner ℝ u x) = 0 := by
    field_simp
    <;> ring
  rw [inv_mul_cancel₀ hb,one_smul,add_assoc,← add_smul,he,zero_smul,add_zero]

noncomputable def stretchEquiv (u : F) {a b : ℝ} (hu : ‖u‖ = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) : F ≃L[ℝ] F :=
  { stretch u a b with
    invFun := stretch u a⁻¹ b⁻¹
    left_inv := fun x => stretch_stretch u x hu ha hb
    right_inv := fun x => by
      have hh := stretch_stretch u x hu (inv_ne_zero ha) (inv_ne_zero hb)
      simpa using hh }

theorem stretch_norm_sq (u x : F) (a b : ℝ) (hu : ‖u‖ = 1) :
    ‖stretch u a b x‖^2 = a^2*(inner ℝ u x)^2+b^2*(‖x‖^2-(inner ℝ u x)^2) := by
  rw [stretch_apply,norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu,one_pow,mul_one,
    real_inner_smul_left,real_inner_smul_right,real_inner_comm x u]
  ring

end LinearDistancePreservers.LatticeMinima

namespace LinearDistancePreservers.LatticeMinima
open scoped RealInnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]

theorem shifted_stretch_norm_sq (u w : F) (c a b : ℝ) (hu : ‖u‖ = 1) :
    ‖c • u+stretch u a b w‖^2 =
      (c+a*inner ℝ u w)^2+b^2*(‖w‖^2-(inner ℝ u w)^2) := by
  rw [norm_add_sq_real,stretch_norm_sq u w a b hu,real_inner_smul_left,
    inner_stretch u w a b hu,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu]
  ring

/-- The unit ball maps into the spherical cap under its explicit axial
and transverse dilation. This does not use lattice geometry. -/
theorem cap_ellipsoid_inside (u w : F) (R h : ℝ) (hu : ‖u‖ = 1)
    (hh : 0 < h) (hR : h ≤ R) (hw : ‖w‖ ≤ 1) :
    ‖(R-h/2) • u+stretch u (h/4) (Real.sqrt (R*h)/2) w‖ ≤ R ∧
    R-h < inner ℝ u ((R-h/2) • u+stretch u (h/4) (Real.sqrt (R*h)/2) w) := by
  have hR0 : 0 < R := hh.trans_le hR
  have hs := abs_real_inner_le_norm u w
  rw [hu,one_mul] at hs
  have hs1 := abs_le.mp (hs.trans hw)
  have hsq : (Real.sqrt (R*h)/2)^2 = R*h/4 := by
    rw [div_pow,Real.sq_sqrt (by positivity)]; norm_num
  have hw2 : ‖w‖^2 ≤ 1 := by nlinarith [norm_nonneg w]
  have ha0 : 0 ≤ R-h/2+(h/4)*inner ℝ u w := by nlinarith
  have ha1 : R-h/2+(h/4)*inner ℝ u w ≤ R-h/4 := by nlinarith
  have ha2 : (R-h/2+(h/4)*inner ℝ u w)^2 ≤ (R-h/4)^2 := by nlinarith
  constructor
  · have hn := shifted_stretch_norm_sq u w (R-h/2) (h/4) (Real.sqrt (R*h)/2) hu
    rw [hsq] at hn
    have hp : R*h/4*(‖w‖^2-(inner ℝ u w)^2) ≤ R*h/4 := by
      exact mul_le_of_le_one_right (by positivity) (by nlinarith [sq_nonneg (inner ℝ u w)])
    nlinarith [norm_nonneg ((R-h/2) • u+stretch u (h/4) (Real.sqrt (R*h)/2) w)]
  · rw [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,
      inner_stretch u w (h/4) (Real.sqrt (R*h)/2) hu]
    nlinarith

/-- Exact inverse-ellipsoid norm after translating along its axis. -/
theorem shifted_inverse_norm_sq (u x : F) (c a b : ℝ) (hu : ‖u‖ = 1) :
    ‖stretch u a⁻¹ b⁻¹ (x-c • u)‖^2 =
      a⁻¹^2*(inner ℝ u x-c)^2+b⁻¹^2*(‖x‖^2-(inner ℝ u x)^2) := by
  rw [stretch_norm_sq u (x-c • u) a⁻¹ b⁻¹ hu,norm_sub_sq_real,
    inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,
    real_inner_smul_right,real_inner_comm x u,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu]
  ring

/-- Every point of the cap lies in the fourfold dilation of the same
explicit ellipsoid. -/
theorem cap_ellipsoid_outside (u x : F) (R h : ℝ) (hu : ‖u‖ = 1)
    (hh : 0 < h) (hR : h ≤ R) (hx : ‖x‖ ≤ R) (hxs : R-h < inner ℝ u x) :
    ‖stretch u (h/4)⁻¹ (Real.sqrt (R*h)/2)⁻¹ (x-(R-h/2) • u)‖ ≤ 4 := by
  have hR0 : 0 < R := hh.trans_le hR
  have hrh : 0 < R*h := mul_pos hR0 hh
  have hs : inner ℝ u x ≤ R := by
    have hh := real_inner_le_norm u x
    simpa [hu] using hh.trans (by simpa [hu] using hx)
  have hs0 : 0 ≤ inner ℝ u x := by linarith
  have ht : (inner ℝ u x-(R-h/2))^2 ≤ (h/2)^2 := by nlinarith
  have hn : ‖x‖^2 ≤ R^2 := by nlinarith [norm_nonneg x]
  have hp : ‖x‖^2-(inner ℝ u x)^2 ≤ 2*R*h := by nlinarith
  have ha : (h/4)⁻¹^2*(inner ℝ u x-(R-h/2))^2 ≤ 4 := by
    rw [inv_pow,inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < (h/4)^2)).mpr
    nlinarith
  have hb : (Real.sqrt (R*h)/2)⁻¹^2*(‖x‖^2-(inner ℝ u x)^2) ≤ 8 := by
    rw [inv_pow,inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < (Real.sqrt (R*h)/2)^2)).mpr
    rw [div_pow,Real.sq_sqrt hrh.le]
    norm_num
    nlinarith
  have he := shifted_inverse_norm_sq u x (R-h/2) (h/4) (Real.sqrt (R*h)/2) hu
  nlinarith [norm_nonneg (stretch u (h/4)⁻¹ (Real.sqrt (R*h)/2)⁻¹ (x-(R-h/2) • u))]


variable [MeasurableSpace F] [BorelSpace F]

/-- Dimension-only lattice flatness for a spherical cap, proved from the
explicit ellipsoid sandwich and Euclidean transference. -/
theorem exists_width_of_empty_cap (L : Submodule ℤ F) [DiscreteTopology L]
    [IsZLattice ℝ L] {n : ℕ} (hdim : Module.finrank ℝ F = n+1)
    (u : F) (R h : ℝ) (hu : ‖u‖ = 1) (hh : 0 < h) (hR : h ≤ R)
    (hempty : ∀ z ∈ L, ¬ (‖z‖ ≤ R ∧ R-h < inner ℝ u z)) :
    ∃ q : F, q ≠ 0 ∧ (∀ z ∈ L, ∃ k : ℤ, inner ℝ q z = (k : ℝ)) ∧
      ∀ x y : F, (‖x‖ ≤ R ∧ R-h < inner ℝ u x) →
        (‖y‖ ≤ R ∧ R-h < inner ℝ u y) →
        inner ℝ q x-inner ℝ q y ≤ 8*((n+1 : ℕ) : ℝ)^(n+2) := by
  have hR0 : 0 < R := hh.trans_le hR
  let T := stretchEquiv u hu (by positivity : h/4 ≠ 0)
    (by positivity : Real.sqrt (R*h)/2 ≠ 0)
  let c := (R-h/2) • u
  have hfree : ∀ z ∈ L, (1 : ℝ) ≤ ‖T.symm (z-c)‖ := by
    intro z hz
    by_contra hn
    have hw : ‖T.symm (z-c)‖ ≤ 1 := (lt_of_not_ge hn).le
    have hin := cap_ellipsoid_inside u (T.symm (z-c)) R h hu hh hR hw
    have he : c+stretch u (h/4) (Real.sqrt (R*h)/2) (T.symm (z-c)) = z := by
      change c+T (T.symm (z-c)) = z
      rw [T.apply_symm_apply]; abel
    change ‖c+stretch u (h/4) (Real.sqrt (R*h)/2) (T.symm (z-c))‖ ≤ R ∧
      R-h < inner ℝ u (c+stretch u (h/4) (Real.sqrt (R*h)/2) (T.symm (z-c))) at hin
    rw [he] at hin
    exact hempty z hz hin
  obtain ⟨q,hq,hint,hwidth⟩ := exists_width_of_empty_ellipsoid L hdim T c
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 4) hfree
  refine ⟨q,hq,hint,?_⟩
  intro x y hx hy
  have hxb : ‖T.symm (x-c)‖ ≤ 4 := cap_ellipsoid_outside u x R h hu hh hR hx.1 hx.2
  have hyb : ‖T.symm (y-c)‖ ≤ 4 := cap_ellipsoid_outside u y R h hu hh hR hy.1 hy.2
  have hw := hwidth x y hxb hyb
  norm_num only [Nat.cast_add,Nat.cast_one,div_one] at hw ⊢
  linarith

end LinearDistancePreservers.LatticeMinima

namespace LinearDistancePreservers.LatticeCaps
open scoped RealInnerProductSpace

/-- Translation between the coordinate cap and its genuine Euclidean norm. -/
theorem mem_cap_iff_norm_inner {d : ℕ} (u x : EuclideanSpace ℝ (Fin d))
    (R h : ℝ) (hR : 0 ≤ R) :
    (fun i => x i) ∈ cap (fun i => u i) R h ↔
      ‖x‖ ≤ R ∧ R-h < inner ℝ u x := by
  have he : normSq (fun i => x i) = ‖x‖^2 := (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [cap,Set.mem_setOf_eq,he,LatticeBody.dot_eq_inner]
  constructor
  · rintro ⟨hn,hs⟩; exact ⟨by nlinarith [norm_nonneg x],hs⟩
  · rintro ⟨hn,hs⟩; exact ⟨by nlinarith [norm_nonneg x],hs⟩

/-- Actual integer flatness for every lattice-point-free spherical cap.
The nonzero integral normal is constructed, with a dimension-only width;
it is not a certificate required from the caller. -/
theorem exists_integer_cap_width {n : ℕ} (u : Fin (n+1) → ℝ) (R h : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hempty : ∀ z : Fin (n+1) → ℤ, LatticeHull.realVector z ∉ cap u R h) :
    ∃ q : Fin (n+1) → ℤ, q ≠ 0 ∧
      ∀ x ∈ cap u R h, ∀ y ∈ cap u R h,
        dot (LatticeHull.realVector q) x-dot (LatticeHull.realVector q) y ≤
          8*((n+1 : ℕ) : ℝ)^(n+2) := by
  classical
  let E := EuclideanSpace ℝ (Fin (n+1))
  let e := EuclideanSpace.basisFun (Fin (n+1)) ℝ
  let L := Submodule.span ℤ (Set.range e.toBasis)
  let uE : E := WithLp.toLp 2 u
  have huE : ‖uE‖ = 1 := by
    have he := EuclideanSpace.real_norm_sq_eq uE
    change ‖uE‖^2 = normSq u at he
    rw [hu] at he
    nlinarith [norm_nonneg uE]
  have hfree : ∀ z ∈ L, ¬ (‖z‖ ≤ R ∧ R-h < inner ℝ uE z) := by
    intro z hz hc
    have hcoord := (e.toBasis.mem_span_iff_repr_mem ℤ z).mp hz
    have hzint : ∀ i, ∃ k : ℤ, (k : ℝ) = z i := by
      intro i
      simpa [e,EuclideanSpace.basisFun_repr] using hcoord i
    choose k hk using hzint
    have hkz : LatticeHull.realVector k = fun i => z i := by funext i; exact hk i
    apply hempty k
    rw [hkz]
    exact (mem_cap_iff_norm_inner uE z R h (hh.trans_le hR).le).mpr hc
  obtain ⟨q,hq,hint,hw⟩ := LatticeMinima.exists_width_of_empty_cap L
    (by simp [E] : Module.finrank ℝ E = n+1) uE R h huE hh hR hfree
  have hqint : ∀ i, ∃ k : ℤ, q i = (k : ℝ) := by
    intro i
    have hh := hint (e i) (Submodule.subset_span (Set.mem_range_self i))
    change ∃ k : ℤ, inner ℝ q (EuclideanSpace.basisFun (Fin (n+1)) ℝ i) = (k : ℝ) at hh
    simpa only [EuclideanSpace.inner_basisFun_real] using hh
  choose k hk using hqint
  have hqk : q = LatticeBody.vector k := by ext i; exact hk i
  refine ⟨k,?_,?_⟩
  · intro hkzero
    apply hq
    rw [hqk,hkzero]
    ext i
    simp [LatticeBody.vector,LatticeHull.realVector]
  · intro x hx y hy
    have hx' := (mem_cap_iff_norm_inner uE (WithLp.toLp 2 x) R h (hh.trans_le hR).le).mp hx
    have hy' := (mem_cap_iff_norm_inner uE (WithLp.toLp 2 y) R h (hh.trans_le hR).le).mp hy
    have hh := hw (WithLp.toLp 2 x) (WithLp.toLp 2 y) hx' hy'
    rw [hqk,← LatticeBody.dot_eq_inner,← LatticeBody.dot_eq_inner] at hh
    exact hh

/-- The constructed integer normal also satisfies the quantitative norm
bound consumed by the deep-cap arithmetic grouping. -/
theorem exists_integer_cap_width_norm {n : ℕ} (u : Fin (n+1) → ℝ) (R h : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hempty : ∀ z : Fin (n+1) → ℤ, LatticeHull.realVector z ∉ cap u R h) :
    ∃ q : Fin (n+1) → ℤ, q ≠ 0 ∧
      (∀ x ∈ cap u R h, ∀ y ∈ cap u R h,
        dot (LatticeHull.realVector q) x-dot (LatticeHull.realVector q) y ≤
          8*((n+1 : ℕ) : ℝ)^(n+2)) ∧
      h^2*normSq (LatticeHull.realVector q) ≤
        5*(8*((n+1 : ℕ) : ℝ)^(n+2))^2 := by
  obtain ⟨q,hq,hw⟩ := exists_integer_cap_width u R h hu hh hR hempty
  exact ⟨q,hq,hw,cap_width_normSq u (LatticeHull.realVector q) R h _ hu hh hR hw⟩

end LinearDistancePreservers.LatticeCaps
