import LinearDistancePreservers.LatticeFlatness
import LinearDistancePreservers.LatticeShells

namespace LinearDistancePreservers.LatticeCaps
open Finset
variable {D : Type*} [Fintype D]

/-- The stronger transverse part of the cap-width inequality, retaining
R*h rather than weakening it to h². -/
theorem cap_width_transverse_normSq (u q : D → ℝ) (R h W : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hw : ∀ x ∈ cap u R h, ∀ y ∈ cap u R h, dot q x-dot q y ≤ W) :
    R*h*(normSq q-(dot u q)^2) ≤ W^2 := by
  let a := dot u q
  let v : D → ℝ := fun i => q i-a*u i
  have hv : dot u v = 0 := by
    dsimp [v,dot]
    simp only [mul_sub,sum_sub_distrib]
    have he : (∑ i, u i*(a*u i)) = a*normSq u := by
      unfold normSq
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [he,hu,mul_one]
    change a-a = 0
    ring
  have hq : q = fun i => a*u i+v i := by funext i; dsimp [v]; ring
  have hnorm : normSq q = a^2+normSq v := by
    conv_lhs => rw [hq]
    exact normSq_axial u v a hu hv
  have hqv : dot q v = normSq v := by
    rw [dot_comm q v]
    conv_lhs => rw [hq]
    rw [dot_add_smul,dot_comm v u,hv]
    simp [dot,normSq,pow_two]
  have hV0 := normSq_nonneg v
  have hperp : R*h*normSq v ≤ W^2 := by
    by_cases hv0 : normSq v = 0
    · rw [hv0,mul_zero]; positivity
    have hV : 0 < normSq v := lt_of_le_of_ne hV0 (Ne.symm hv0)
    have hRpos : 0 < R := hh.trans_le hR
    let c := Real.sqrt (R*h*normSq v)/(2*normSq v)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hsqrt : Real.sqrt (R*h*normSq v)^2 = R*h*normSq v := Real.sq_sqrt (by positivity)
    let y : D → ℝ := fun i => c*v i
    have hy : dot u y = 0 := by
      have he := dot_add_smul u v (fun _ => 0) c
      rw [hv] at he
      simpa [y,dot] using he
    have hqy : dot q y = c*normSq v := by
      have he := dot_add_smul q v (fun _ => 0) c
      rw [hqv] at he
      simpa [y,dot] using he
    have hyR : normSq y = R*h/4 := by
      rw [show normSq y = c^2*normSq v from normSq_smul v c]
      dsimp [c]
      field_simp
      nlinarith
    have ht := cap_width_transverse u q y R h W hu hy hh hR hyR.le hw
    rw [hqy,abs_of_nonneg (mul_nonneg hc hV0)] at ht
    have he : 2*(c*normSq v) = Real.sqrt (R*h*normSq v) := by
      dsimp [c]
      field_simp
    rw [he] at ht
    have ht2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
    rw [hsqrt] at ht2
    nlinarith
  rw [hnorm]
  dsimp [a] at *
  nlinarith

/-- The cap apex belongs to the strict-height cap. -/
theorem apex_mem_cap (u : D → ℝ) (R h : ℝ) (hu : normSq u = 1) (hh : 0 < h) :
    (fun i => R*u i) ∈ cap u R h := by
  constructor
  · rw [normSq_smul,hu,mul_one]
  · have he := dot_axial u (fun _ => 0) R hu (by simp [dot])
    simp only [add_zero] at he
    rw [he]; linarith

/-- Every cap point lies in a fixed-width normal slab around its apex. -/
theorem cap_width_apex_band (u q : D → ℝ) (R h W : ℝ)
    (hu : normSq u = 1) (hh : 0 < h)
    (hw : ∀ x ∈ cap u R h, ∀ y ∈ cap u R h, dot q x-dot q y ≤ W)
    (x : D → ℝ) (hx : x ∈ cap u R h) :
    |dot q x-R*dot u q| ≤ W := by
  have ha := apex_mem_cap u R h hu hh
  have h1 := hw x hx _ ha
  have h2 := hw _ ha x hx
  have he : dot q (fun i => R*u i) = R*dot u q := by
    have he := dot_add_smul q u (fun _ => 0) R
    have he' : dot q (fun i => R*u i) = R*dot q u := by simpa [dot] using he
    rwa [dot_comm q u] at he'
  rw [he] at h1 h2
  exact abs_le.mpr ⟨by linarith,h1⟩

/-- Once the normal is oriented toward the cap, its apex depth K and
height h satisfy K*||q||*h ≤ W². This removes trigonometry and facet data
from the normal/depth restriction. -/
theorem cap_width_depth_height (u q : D → ℝ) (R h W p : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hp : 0 ≤ p) (hp2 : p^2 = normSq q) (hs : 0 ≤ dot u q)
    (hw : ∀ x ∈ cap u R h, ∀ y ∈ cap u R h, dot q x-dot q y ≤ W) :
    R*(p-dot u q)*p*h ≤ W^2 := by
  have ht := cap_width_transverse_normSq u q R h W hu hh hR hw
  have hcs := sum_mul_sq_le_sq_mul_sq univ u q
  change (dot u q)^2 ≤ normSq u*normSq q at hcs
  rw [hu,one_mul,← hp2] at hcs
  have hsp : dot u q ≤ p := by nlinarith
  have hm : p*(p-dot u q) ≤ p^2-(dot u q)^2 := by nlinarith
  have hR0 : 0 < R := hh.trans_le hR
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ R*h)
  rw [← hp2] at ht
  nlinarith

/-- The cap width also controls height times the normal length. -/
theorem cap_width_height_norm (u q : D → ℝ) (R h W p : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hp : 0 ≤ p) (hp2 : p^2 = normSq q)
    (hw : ∀ x ∈ cap u R h, ∀ y ∈ cap u R h, dot q x-dot q y ≤ W) :
    h*p ≤ 3*W := by
  have ha := apex_mem_cap u R h hu hh
  have hW : 0 ≤ W := by simpa using hw _ ha _ ha
  have hn := cap_width_normSq u q R h W hu hh hR hw
  rw [← hp2] at hn
  have hhp : 0 ≤ h*p := mul_nonneg hh.le hp
  nlinarith [sq_nonneg (h*p-3*W)]

/-- Rounding the nonnegative apex depth retains every positive depth,
including the nearly parallel-normal case k=1. -/
theorem rounded_depth_bounds (K p h W : ℝ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hh : 0 ≤ h) (hdepth : K*p*h ≤ W^2) (hheight : h*p ≤ 3*W) :
    1 ≤ ⌊K⌋₊+1 ∧ K < (⌊K⌋₊+1 : ℕ) ∧
      ((⌊K⌋₊+1 : ℕ) : ℝ)*p*h ≤ W^2+3*W := by
  refine ⟨by omega,?_,?_⟩
  · exact_mod_cast Nat.lt_floor_add_one K
  · have hf := Nat.floor_le hK
    have hm := mul_le_mul_of_nonneg_right (by norm_num only [Nat.cast_add,Nat.cast_one]; linarith :
      ((⌊K⌋₊+1 : ℕ) : ℝ) ≤ K+1) (mul_nonneg hp hh)
    nlinarith

/-- The strict-shell and normal-slab cell associated to one integer
normal and one positive depth index. -/
def depthCell (d : ℕ) (R W C : ℝ) (q : Fin d → ℤ) (k : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ‖x‖ ≤ R ∧ R-C/((k : ℝ)*LatticeShells.radius q) < ‖x‖ ∧
    |dot (LatticeHull.realVector q) (fun i => x i)-
      (R*LatticeShells.radius q-k)| ≤ W+1}


theorem one_le_integer_radius {d : ℕ} (q : Fin d → ℤ) (hq : q ≠ 0) :
    1 ≤ LatticeShells.radius q := by
  obtain ⟨i,hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra! hn
    exact hq (funext hn)
  have hqi : (1 : ℤ) ≤ |q i| := by have := abs_pos.mpr hi; omega
  have hqi' : (1 : ℝ) ≤ |(q i : ℝ)| := by exact_mod_cast hqi
  exact hqi'.trans (LatticeShells.coord_le_radius q i)

/-- Every point of one cap lies in one common normal/depth cell, with
the exact product restriction needed by the finite double sum. -/
theorem cap_subset_depthCell {d : ℕ} (u : Fin d → ℝ) (q : Fin d → ℤ)
    (R h W : ℝ) (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hq : q ≠ 0) (hs : 0 ≤ dot u (LatticeHull.realVector q))
    (hw : ∀ x ∈ cap u R h, ∀ y ∈ cap u R h,
      dot (LatticeHull.realVector q) x-dot (LatticeHull.realVector q) y ≤ W) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ)*LatticeShells.radius q*h ≤ W^2+3*W ∧
      ∀ x : EuclideanSpace ℝ (Fin d), (fun i => x i) ∈ cap u R h →
        x ∈ depthCell d R W (W^2+3*W) q k := by
  let p := LatticeShells.radius q
  let s := dot u (LatticeHull.realVector q)
  let K := R*(p-s)
  have hp1 : 1 ≤ p := one_le_integer_radius q hq
  have hp : 0 < p := by linarith
  have hp2 : p^2 = normSq (LatticeHull.realVector q) :=
    Real.sq_sqrt (normSq_nonneg _)
  have hcs := sum_mul_sq_le_sq_mul_sq univ u (LatticeHull.realVector q)
  change s^2 ≤ normSq u*normSq (LatticeHull.realVector q) at hcs
  rw [hu,one_mul,← hp2] at hcs
  have hsp : s ≤ p := by dsimp [s] at *; nlinarith
  have hR0 : 0 < R := hh.trans_le hR
  have hK : 0 ≤ K := mul_nonneg hR0.le (sub_nonneg.mpr hsp)
  have hd : K*p*h ≤ W^2 := cap_width_depth_height u _ R h W p hu hh hR hp.le hp2 hs hw
  have hhp : h*p ≤ 3*W := cap_width_height_norm u _ R h W p hu hh hR hp.le hp2 hw
  obtain ⟨hk,hKk,hbound⟩ := rounded_depth_bounds K p h W hK hp.le hh.le hd hhp
  refine ⟨⌊K⌋₊+1,hk,hbound,?_⟩
  intro x hx
  have hkpos : (0 : ℝ) < (⌊K⌋₊+1 : ℕ) := by positivity
  have hheight : h ≤ (W^2+3*W)/((⌊K⌋₊+1 : ℕ)*p) := by
    apply (le_div_iff₀ (mul_pos hkpos hp)).mpr
    nlinarith
  have hshell := cap_subset_shell u R h hu hR hx
  have hnorm : normSq (fun i => x i) = ‖x‖^2 := (EuclideanSpace.real_norm_sq_eq x).symm
  change (R-h)^2 < normSq (fun i => x i) ∧ normSq (fun i => x i) ≤ R^2 at hshell
  rw [hnorm] at hshell
  have hxR : ‖x‖ ≤ R := by nlinarith [norm_nonneg x]
  have hxh : R-h < ‖x‖ := by nlinarith [norm_nonneg x]
  have hband := cap_width_apex_band u (LatticeHull.realVector q) R h W hu hh hw _ hx
  have hfloor := Nat.floor_le hK
  have hkupper : ((⌊K⌋₊+1 : ℕ) : ℝ) ≤ K+1 := by norm_num only [Nat.cast_add,Nat.cast_one]; linarith
  refine ⟨hxR,by change R-(W^2+3*W)/((⌊K⌋₊+1 : ℕ)*p) < ‖x‖; linarith,?_⟩
  apply abs_le.mpr
  have hb := abs_le.mp hband
  change -(W+1) ≤ dot (LatticeHull.realVector q) (fun i => x i)-(R*p-(⌊K⌋₊+1 : ℕ)) ∧
    dot (LatticeHull.realVector q) (fun i => x i)-(R*p-(⌊K⌋₊+1 : ℕ)) ≤ W+1
  dsimp [K,s] at hKk hkupper
  constructor <;> linarith


theorem realVector_neg {d : ℕ} (q : Fin d → ℤ) :
    LatticeHull.realVector (-q) = fun i => -LatticeHull.realVector q i := by
  funext i
  simp [LatticeHull.realVector]

theorem dot_neg_left (q x : D → ℝ) : dot (fun i => -q i) x = -dot q x := by
  simp [dot]

theorem dot_neg_right (q x : D → ℝ) : dot q (fun i => -x i) = -dot q x := by
  simp [dot]

/-- A flatness normal can be oriented toward the cap without changing
integrality, nonzeroness, or its width bound. -/
theorem exists_oriented_integer_cap_width {n : ℕ} (u : Fin (n+1) → ℝ) (R h : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hempty : ∀ z : Fin (n+1) → ℤ, LatticeHull.realVector z ∉ cap u R h) :
    ∃ q : Fin (n+1) → ℤ, q ≠ 0 ∧ 0 ≤ dot u (LatticeHull.realVector q) ∧
      ∀ x ∈ cap u R h, ∀ y ∈ cap u R h,
        dot (LatticeHull.realVector q) x-dot (LatticeHull.realVector q) y ≤
          8*((n+1 : ℕ) : ℝ)^(n+2) := by
  obtain ⟨q,hq,hw⟩ := exists_integer_cap_width u R h hu hh hR hempty
  by_cases hs : 0 ≤ dot u (LatticeHull.realVector q)
  · exact ⟨q,hq,hs,hw⟩
  refine ⟨-q,neg_ne_zero.mpr hq,?_,?_⟩
  · rw [realVector_neg,dot_neg_right]
    linarith
  · intro x hx y hy
    rw [realVector_neg,dot_neg_left,dot_neg_left]
    have hh := hw y hy x hx
    linarith

/-- A product restriction on integer depth and Euclidean normal length
places the normal in the exact finite box with floor-divided radius. -/
theorem normal_depth_in_box {d M k : ℕ} (q : Fin d → ℤ) (hq : q ≠ 0)
    (hk : 1 ≤ k) (hbound : (k : ℝ)*LatticeShells.radius q ≤ M) :
    k ∈ Finset.Icc 1 M ∧ q ∈ LatticeShells.box d (M/k) := by
  have hp := one_le_integer_radius q hq
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) ≤ k := by positivity
  constructor
  · apply Finset.mem_Icc.mpr
    refine ⟨hk,?_⟩
    have hh : (k : ℝ) ≤ M := by nlinarith
    exact_mod_cast hh
  · apply Fintype.mem_piFinset.mpr
    intro i
    have hc := LatticeShells.coord_le_radius q i
    have hi : (k : ℝ)*|(q i : ℝ)| ≤ M := (mul_le_mul_of_nonneg_left hc hkR).trans hbound
    have hiZ : (k : ℤ)*|q i| ≤ M := by exact_mod_cast hi
    rw [← Int.natCast_natAbs] at hiZ
    have hiN : k*(q i).natAbs ≤ M := by exact_mod_cast hiZ
    have hdiv : (q i).natAbs ≤ M/k := (Nat.le_div_iff_mul_le hk0).mpr (by simpa [mul_comm] using hiN)
    have habs : |q i| ≤ (M/k : ℕ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hdiv
    exact Finset.mem_Icc.mpr (abs_le.mp habs)


noncomputable def flatnessWidth (n : ℕ) : ℝ := 8*((n+1 : ℕ) : ℝ)^(n+2)
noncomputable def depthConstant (n : ℕ) : ℝ := (flatnessWidth n)^2+3*flatnessWidth n
noncomputable def depthRadius (n : ℕ) (δ : ℝ) : ℕ := ⌈depthConstant n/δ⌉₊

/-- A finite, explicit union of integer-normal/depth shell cells. -/
def deepCells (n : ℕ) (R δ : ℝ) : Set (EuclideanSpace ℝ (Fin (n+1))) :=
  ⋃ k ∈ Finset.Icc 1 (depthRadius n δ),
    ⋃ q ∈ LatticeShells.box (n+1) (depthRadius n δ/k),
      depthCell (n+1) R (flatnessWidth n) (depthConstant n) q k

/-- The actual missed region is covered by the shallow caps plus these
finitely many cells. Every integer normal is constructed by flatness, and
the floor-divided normal ranges are proved, not supplied as an oracle. -/
theorem missed_subset_shallow_union_deep (n R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) R \ LatticeBody.body (n+1) R ⊆
      shallowCaps (n+1) R δ ∪ deepCells n R δ := by
  intro x hx
  obtain ⟨u,h,hu,hh,hhR,hxcap,hfree⟩ := LatticeBody.missed_mem_support_cap hx
  by_cases hsmall : h ≤ δ
  · exact Or.inl ⟨u,h,hu,hh,hsmall,hxcap⟩
  have hδh : δ < h := lt_of_not_ge hsmall
  have hhpos : 0 < h := hδ.trans hδh
  obtain ⟨q,hq,hs,hw⟩ := exists_oriented_integer_cap_width u R h hu hhpos hhR hfree
  obtain ⟨k,hk,hbound,hcover⟩ := cap_subset_depthCell u q R h (flatnessWidth n)
    hu hhpos hhR hq hs hw
  have hp : 0 ≤ LatticeShells.radius q := (zero_le_one.trans (one_le_integer_radius q hq))
  have hkp : 0 ≤ (k : ℝ)*LatticeShells.radius q := mul_nonneg (Nat.cast_nonneg k) hp
  have hδbound : (k : ℝ)*LatticeShells.radius q ≤ depthConstant n/δ := by
    apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hδh.le hkp
    exact hh.trans hbound
  have hM : (k : ℝ)*LatticeShells.radius q ≤ depthRadius n δ :=
    hδbound.trans (Nat.le_ceil _)
  obtain ⟨hkM,hqM⟩ := normal_depth_in_box q hq hk hM
  apply Or.inr
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkM,
    Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨hqM,hcover x hxcap⟩⟩⟩⟩

/-- The harmless zero-normal terms in the finite index set contribute
no cell at all, matching the zero term in the weighted normal sum. -/
theorem depthCell_zero (d : ℕ) (R W C : ℝ) (k : ℕ) :
    depthCell d R W C 0 k = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h0 : LatticeShells.radius (0 : Fin d → ℤ) = 0 := by
    simp [LatticeShells.radius]
  have hh := hx.2.1
  rw [h0,mul_zero,div_zero,sub_zero] at hh
  exact (not_lt_of_ge hx.1) hh

end LinearDistancePreservers.LatticeCaps
