import LinearDistancePreservers.LatticeCapVolume
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

namespace LinearDistancePreservers.LatticeBody
open Set Metric
open scoped RealInnerProductSpace

/-- The same integer vectors, now in the Euclidean space carrying volume. -/
def vector {d : ℕ} (z : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (LatticeHull.realVector z)

noncomputable def body (d R : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (vector '' (LatticeHull.ball d R : Set (Fin d → ℤ)))

theorem isCompact_body (d R : ℕ) : IsCompact (body d R) :=
  ((LatticeHull.ball d R).finite_toSet.image vector).isCompact_convexHull ℝ

theorem body_eq_image (d R : ℕ) :
    body d R = (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm ''
      convexHull ℝ (LatticeHull.realVector '' (LatticeHull.ball d R : Set (Fin d → ℤ))) := by
  change body d R = (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap '' _
  rw [LinearMap.image_convexHull]
  simp only [body,Set.image_image,vector]
  rfl

/-- The graph-facing finite vertex set is exactly the complete extreme-point
set of the Euclidean body, not only a subset or a different normed hull. -/
theorem image_vertices (d R : ℕ) :
    vector '' (LatticeHull.vertices (LatticeHull.ball d R) : Set (Fin d → ℤ)) =
      (body d R).extremePoints ℝ := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm
  calc
    _ = e '' (LatticeHull.realVector '' (LatticeHull.vertices (LatticeHull.ball d R) : Set (Fin d → ℤ))) := by
      rw [Set.image_image]; rfl
    _ = e '' (convexHull ℝ (LatticeHull.realVector '' (LatticeHull.ball d R : Set (Fin d → ℤ)))).extremePoints ℝ := by
      rw [LatticeHull.image_vertices]
    _ = (body d R).extremePoints ℝ := by
      rw [image_extremePoints]
      rw [body_eq_image]

theorem vector_mem_closedBall_iff {d R : ℕ} (z : Fin d → ℤ) :
    vector z ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) R ↔ z ∈ LatticeHull.ball d R := by
  rw [LatticeHull.mem_ball]
  have he : ‖vector z‖^2 = ∑ i, (z i : ℝ)^2 := by
    simpa [vector,LatticeHull.realVector] using EuclideanSpace.real_norm_sq_eq (vector z)
  have hn := norm_nonneg (vector z)
  have hR : (0 : ℝ) ≤ R := by positivity
  simp only [mem_closedBall,dist_zero_right]
  constructor
  · intro h
    have hh : (∑ i, (z i : ℝ)^2) ≤ (R : ℝ)^2 := by nlinarith
    exact_mod_cast hh
  · intro h
    have hh : (∑ i, (z i : ℝ)^2) ≤ (R : ℝ)^2 := by exact_mod_cast h
    nlinarith

theorem body_subset_closedBall (d R : ℕ) :
    body d R ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) R := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨z,hz,rfl⟩
  exact (vector_mem_closedBall_iff z).mpr hz

theorem zero_mem_body (d R : ℕ) : (0 : EuclideanSpace ℝ (Fin d)) ∈ body d R := by
  have hz : (fun _ : Fin d => (0 : ℤ)) ∈ LatticeHull.ball d R := by
    apply LatticeHull.mem_ball.mpr
    simp
  have hh := subset_convexHull ℝ _ (Set.mem_image_of_mem vector hz)
  have he : vector (fun _ : Fin d => (0 : ℤ)) = 0 := by
    ext i
    simp [vector,LatticeHull.realVector]
  rw [he] at hh
  exact hh

/-- A normalized strict separator, obtained from Hahn--Banach and Riesz.
The body is supplied as an actual nonempty closed convex set. -/
theorem exists_unit_separator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {P : Set E}
    (hP : Convex ℝ P) (hclosed : IsClosed P) (hne : P.Nonempty)
    {x : E} (hx : x ∉ P) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ y ∈ P, inner ℝ u y < inner ℝ u x := by
  obtain ⟨f,c,hf,hx'⟩ := geometric_hahn_banach_closed_point hP hclosed hx
  let a := (InnerProductSpace.toDual ℝ E).symm f
  have ha (y : E) : inner ℝ a y = f y := InnerProductSpace.toDual_symm_apply
  have ha0 : a ≠ 0 := by
    intro heq
    obtain ⟨y,hy⟩ := hne
    have hlt := (hf y hy).trans hx'
    rw [← ha y,← ha x,heq] at hlt
    simp at hlt
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  refine ⟨‖a‖⁻¹ • a,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnorm),inv_mul_cancel₀ hnorm.ne']
  · intro y hy
    simp only [real_inner_smul_left,ha]
    exact mul_lt_mul_of_pos_left ((hf y hy).trans hx') (inv_pos.mpr hnorm)

theorem dot_eq_inner {d : ℕ} (u x : EuclideanSpace ℝ (Fin d)) :
    LatticeCaps.dot (fun i => u i) (fun i => x i) = inner ℝ u x := by
  simp [LatticeCaps.dot,PiLp.inner_apply,mul_comm]

/-- Every point missed by the actual integer hull belongs to an attained,
lattice-free support cap. No facet enumeration or geometric oracle is assumed. -/
theorem missed_mem_support_cap {d R : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ closedBall 0 R \ body d R) :
    ∃ (u : Fin d → ℝ) (h : ℝ), LatticeCaps.normSq u = 1 ∧ 0 ≤ h ∧ h ≤ R ∧
      (fun i => x i) ∈ LatticeCaps.cap u R h ∧
      ∀ z : Fin d → ℤ, LatticeHull.realVector z ∉ LatticeCaps.cap u R h := by
  obtain ⟨u,hu,hsep⟩ := exists_unit_separator (convex_convexHull ℝ _)
    (isCompact_body d R).isClosed ⟨0,zero_mem_body d R⟩ hx.2
  have hu' : LatticeCaps.normSq (fun i => u i) = 1 := by
    change (∑ i, (u i)^2) = 1
    rw [← EuclideanSpace.real_norm_sq_eq,hu]
    norm_num
  obtain ⟨h,z,hh,hhR,hz,hs,hsall,hfree⟩ := LatticeCaps.exists_touching_lattice_free_cap (R := R) (fun i => u i) hu'
  refine ⟨(fun i => u i),h,hu',hh,hhR,?_,hfree⟩
  constructor
  · have hnorm : ‖x‖ ≤ (R : ℝ) := by simpa using hx.1
    change (∑ i, (x i)^2) ≤ (R : ℝ)^2
    rw [← EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg x]
  · have hzbody : vector z ∈ body d R := subset_convexHull ℝ _ ⟨z,hz,rfl⟩
    have hlt := hsep (vector z) hzbody
    rw [← dot_eq_inner,← dot_eq_inner] at hlt
    change LatticeCaps.dot (fun i => u i) (LatticeHull.realVector z) <
      LatticeCaps.dot (fun i => u i) (fun i => x i) at hlt
    rw [hs] at hlt
    exact hlt

/-- Any supporting half-space on the finite lattice generators also
contains their actual Euclidean convex hull. -/
theorem support_on_body {d R : ℕ} (u : Fin d → ℝ) (t : ℝ)
    (hs : ∀ z ∈ LatticeHull.ball d R, LatticeCaps.dot u (LatticeHull.realVector z) ≤ t) :
    ∀ x ∈ body d R, LatticeCaps.dot u (fun i => x i) ≤ t := by
  let f := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 u)
  have hf (x : EuclideanSpace ℝ (Fin d)) : f x = LatticeCaps.dot u (fun i => x i) :=
    (dot_eq_inner (WithLp.toLp 2 u) x).symm
  have hc : Convex ℝ {x : EuclideanSpace ℝ (Fin d) | f x ≤ t} :=
    (convex_Iic t).linear_preimage f.toLinearMap
  have hsub : body d R ⊆ {x | f x ≤ t} := by
    apply convexHull_min _ hc
    rintro _ ⟨z,hz,rfl⟩
    change f (vector z) ≤ t
    rw [hf]
    exact hs z hz
  intro x hx
  rw [← hf]
  exact hsub hx

/-- A lattice-free cap is disjoint from the integer hull itself, not only
from the original lattice generators. -/
theorem lattice_free_cap_outside {d R : ℕ} (u : Fin d → ℝ) (h : ℝ)
    (hfree : ∀ z : Fin d → ℤ, LatticeHull.realVector z ∉ LatticeCaps.cap u R h)
    {x : EuclideanSpace ℝ (Fin d)} (hx : (fun i => x i) ∈ LatticeCaps.cap u R h) :
    x ∉ body d R := by
  have hs : ∀ z ∈ LatticeHull.ball d R,
      LatticeCaps.dot u (LatticeHull.realVector z) ≤ (R : ℝ)-h := by
    intro z hz
    by_contra! hlt
    apply hfree z
    refine ⟨?_,hlt⟩
    have hh := LatticeHull.mem_ball.mp hz
    change (∑ i, (z i : ℝ)^2) ≤ (R : ℝ)^2
    exact_mod_cast hh
  intro hxbody
  exact (not_lt_of_ge (support_on_body u _ hs x hxbody)) hx.2

/-- Exact covering of the missed region by actual lattice-free support
caps. Both implications are proved, including boundary conventions. -/
theorem missed_eq_caps (d R : ℕ) :
    closedBall (0 : EuclideanSpace ℝ (Fin d)) R \ body d R =
      {x | ∃ (u : Fin d → ℝ) (h : ℝ), LatticeCaps.normSq u = 1 ∧ 0 ≤ h ∧ h ≤ R ∧
        (fun i => x i) ∈ LatticeCaps.cap u R h ∧
        ∀ z : Fin d → ℤ, LatticeHull.realVector z ∉ LatticeCaps.cap u R h} := by
  ext x
  constructor
  · exact missed_mem_support_cap
  · rintro ⟨u,h,hu,hh,hhR,hx,hfree⟩
    refine ⟨?_,lattice_free_cap_outside u h hfree hx⟩
    simp only [mem_closedBall,dist_zero_right]
    have he := EuclideanSpace.real_norm_sq_eq x
    have hs := hx.1
    change (∑ i, (x i)^2) ≤ (R : ℝ)^2 at hs
    nlinarith [norm_nonneg x,show (0 : ℝ) ≤ R from Nat.cast_nonneg R]

end LinearDistancePreservers.LatticeBody
