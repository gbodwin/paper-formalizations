import LinearDistancePreservers.LatticeHull
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace LinearDistancePreservers.LatticeCaps
open Finset
variable {D : Type*} [Fintype D]

def dot (u x : D → ℝ) : ℝ := ∑ i, u i * x i

def normSq (x : D → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The spherical cap beyond a supporting plane. Its strict half-space
boundary is essential: the supporting lattice face is not removed. -/
def cap (u : D → ℝ) (R h : ℝ) : Set (D → ℝ) :=
  {x | normSq x ≤ R^2 ∧ R-h < dot u x}

theorem normSq_nonneg (x : D → ℝ) : 0 ≤ normSq x :=
  sum_nonneg (fun i _ => sq_nonneg (x i))

theorem dot_axial (u y : D → ℝ) (a : ℝ)
    (hu : normSq u = 1) (hy : dot u y = 0) :
    dot u (fun i => a*u i+y i) = a := by
  calc
    _ = a * normSq u + dot u y := by
      unfold dot normSq
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      ring
    _ = a := by rw [hu,hy]; ring

theorem normSq_axial (u y : D → ℝ) (a : ℝ)
    (hu : normSq u = 1) (hy : dot u y = 0) :
    normSq (fun i => a*u i+y i) = a^2 + normSq y := by
  calc
    _ = a^2 * normSq u + 2*a*dot u y + normSq y := by
      unfold dot normSq
      simp only [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    _ = a^2 + normSq y := by rw [hu,hy]; ring

/-- Every cap cut beyond a support plane of the actual finite integer ball
is lattice-point free; the face on the plane remains allowed. -/
theorem cap_lattice_free {d R : ℕ} (u : Fin d → ℝ) (h : ℝ)
    (hsupport : ∀ z ∈ LatticeHull.ball d R,
      dot u (LatticeHull.realVector z) ≤ (R : ℝ)-h) :
    ∀ z : Fin d → ℤ, LatticeHull.realVector z ∉ cap u R h := by
  intro z hz
  have hball : z ∈ LatticeHull.ball d R := by
    apply LatticeHull.mem_ball.mpr
    have hh := hz.1
    change (∑ i, (z i : ℝ)^2) ≤ (R : ℝ)^2 at hh
    exact_mod_cast hh
  exact (not_lt_of_ge (hsupport z hball)) hz.2

/-- An explicit centered cylinder contained in the cap: axial half-width
h/4 and squared transverse radius R*h/4. This is the anisotropic body to
which a lattice-flatness argument can subsequently be applied. -/
theorem cylinder_mem_cap (u y : D → ℝ) (R h t : ℝ)
    (hu : normSq u = 1) (hy : dot u y = 0)
    (hh : 0 < h) (hR : h ≤ R) (ht : |t| ≤ h/4)
    (hyR : normSq y ≤ R*h/4) :
    (fun i => (R-h/2+t)*u i+y i) ∈ cap u R h := by
  have ht' := abs_le.mp ht
  have ha : 0 ≤ R-h/2+t := by linarith
  have ha' : R-h/2+t ≤ R-h/4 := by linarith
  have hR0 : 0 < R := hh.trans_le hR
  have hs : (R-h/2+t)^2 ≤ (R-h/4)^2 := by nlinarith
  constructor
  · rw [normSq_axial u y _ hu hy]
    nlinarith
  · rw [dot_axial u y _ hu hy]
    linarith

/-- A cap with nonnegative support lies in the corresponding spherical
shell. This is the set inclusion behind the shallow-cap volume estimate. -/
theorem cap_subset_shell (u : D → ℝ) (R h : ℝ)
    (hu : normSq u = 1) (hR : h ≤ R) :
    cap u R h ⊆ {x | (R-h)^2 < normSq x ∧ normSq x ≤ R^2} := by
  intro x hx
  have hc : (dot u x)^2 ≤ normSq x := by
    have hc := sum_mul_sq_le_sq_mul_sq univ u x
    change (dot u x)^2 ≤ normSq u * normSq x at hc
    simpa [hu] using hc
  exact ⟨by have := hx.2; nlinarith, hx.1⟩

/-- Polynomial annulus estimate, with no unspecified asymptotic constant. -/
theorem annulus_power_bound (R h : ℝ) (h0 : 0 ≤ h) (hR : h ≤ R) (n : ℕ) :
    R^(n+1)-(R-h)^(n+1) ≤ (n+1 : ℕ)*R^n*h := by
  have hR0 : 0 ≤ R := h0.trans hR
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (R-h)^(n+1) ≤ R^(n+1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hmul := mul_le_mul_of_nonneg_left ih hR0
    have hmul' := mul_le_mul_of_nonneg_left hp h0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at *
    nlinarith

/-- An actual support maximizer of the finite integer ball exists for
every real direction, independently of any sharp vertex-count estimate. -/
theorem exists_support {d R : ℕ} (u : Fin d → ℝ) :
    ∃ z ∈ LatticeHull.ball d R, ∀ w ∈ LatticeHull.ball d R,
      dot u (LatticeHull.realVector w) ≤ dot u (LatticeHull.realVector z) := by
  classical
  have hz : (fun _ : Fin d => (0 : ℤ)) ∈ LatticeHull.ball d R := by
    apply LatticeHull.mem_ball.mpr
    simp
  exact Finset.exists_max_image _ _ ⟨_,hz⟩

/-- Exact cross-section identity and the two-sided scale comparison used
in the cap proof. No asymptotic notation is hidden in these inequalities. -/
theorem cross_section_bounds (R h : ℝ) (h0 : 0 ≤ h) (hR : h ≤ R) :
    R^2-(R-h)^2 = (2*R-h)*h ∧
      R*h ≤ R^2-(R-h)^2 ∧ R^2-(R-h)^2 ≤ 2*R*h := by
  constructor
  · ring
  constructor <;> nlinarith

/-- In a unit direction, the actual finite ball supplies a touching support
plane, with height between zero and R, whose open cap is lattice-free. -/
theorem exists_touching_lattice_free_cap {d R : ℕ} (u : Fin d → ℝ)
    (hu : normSq u = 1) :
    ∃ (h : ℝ) (z : Fin d → ℤ), 0 ≤ h ∧ h ≤ R ∧
      z ∈ LatticeHull.ball d R ∧ dot u (LatticeHull.realVector z) = (R : ℝ)-h ∧
      (∀ w ∈ LatticeHull.ball d R, dot u (LatticeHull.realVector w) ≤ (R : ℝ)-h) ∧
      ∀ w : Fin d → ℤ, LatticeHull.realVector w ∉ cap u R h := by
  obtain ⟨z,hz,hs⟩ := exists_support (R := R) u
  have hnorm : normSq (LatticeHull.realVector z) ≤ (R : ℝ)^2 := by
    have hz' := LatticeHull.mem_ball.mp hz
    change (∑ i, (z i : ℝ)^2) ≤ (R : ℝ)^2
    exact_mod_cast hz'
  have hdot2 : (dot u (LatticeHull.realVector z))^2 ≤ (R : ℝ)^2 := by
    have hc := sum_mul_sq_le_sq_mul_sq univ u (LatticeHull.realVector z)
    change (dot u (LatticeHull.realVector z))^2 ≤ normSq u * normSq (LatticeHull.realVector z) at hc
    rw [hu,one_mul] at hc
    exact hc.trans hnorm
  have hz0 : (fun _ : Fin d => (0 : ℤ)) ∈ LatticeHull.ball d R := by
    apply LatticeHull.mem_ball.mpr
    simp
  have hdot0 : 0 ≤ dot u (LatticeHull.realVector z) := by
    simpa [dot,LatticeHull.realVector] using hs _ hz0
  have hR0 : (0 : ℝ) ≤ R := by positivity
  let h := (R : ℝ)-dot u (LatticeHull.realVector z)
  have hh : (R : ℝ)-h = dot u (LatticeHull.realVector z) := by dsimp [h]; ring
  have hs' : ∀ w ∈ LatticeHull.ball d R,
      dot u (LatticeHull.realVector w) ≤ (R : ℝ)-h := by rw [hh]; exact hs
  refine ⟨h,z,?_,?_,hz,hh.symm,hs',cap_lattice_free u h hs'⟩
  · dsimp [h]; nlinarith
  · dsimp [h]; linarith

end LinearDistancePreservers.LatticeCaps
