import LinearDistancePreservers.LatticeCellVolume
import LinearDistancePreservers.LatticeApproximation

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric Set Finset

theorem depthCell_subset_closedBall (d : ℕ) (R W C : ℝ) (q : Fin d → ℤ) (k : ℕ) :
    depthCell d R W C q k ⊆ closedBall 0 R := by
  intro x hx
  simpa only [mem_closedBall,dist_zero_right] using hx.1

theorem deepCells_subset_closedBall (n : ℕ) (R δ : ℝ) :
    deepCells n R δ ⊆ closedBall 0 R := by
  intro x hx
  simp only [deepCells,Set.mem_iUnion] at hx
  obtain ⟨k,hk,q,hq,hx⟩ := hx
  exact depthCell_subset_closedBall _ _ _ _ _ _ hx

/-- The finite double sum now bounds the actual union of normal/depth
cells, rather than a caller-supplied volume or facet-count expression. -/
theorem deepCells_volume_bound (n : ℕ) (R δ : ℝ) (hR : 0 < R)
    (hCR : depthConstant (n+2) ≤ R) :
    volume.real (deepCells (n+2) R δ) ≤
      cellCoefficient n (flatnessWidth (n+2)) (depthConstant (n+2))*
        R^(((n : ℝ)+2)/2)*(4*(n+3)*3^(n+2) : ℕ)*
        (depthRadius (n+2) δ : ℝ)^(((n : ℝ)+2)/2) := by
  let W := flatnessWidth (n+2)
  let C := depthConstant (n+2)
  let M := depthRadius (n+2) δ
  let a := ((n : ℝ)+2)/2
  let b := ((n : ℝ)-2)/2
  let c := -((n : ℝ)+4)/2
  let A := cellCoefficient n W C*R^a
  have hW : 0 ≤ W := by dsimp [W,flatnessWidth]; positivity
  have hC : 0 ≤ C := by dsimp [C,depthConstant]; unfold flatnessWidth; positivity
  have hA : 0 ≤ A := by dsimp [A,cellCoefficient]; positivity
  have hkbound (k : ℕ) (hk : k ∈ Finset.Icc 1 M) :
      volume.real (⋃ q ∈ LatticeShells.box (n+3) (M/k), depthCell (n+3) R W C q k) ≤
        A*(k : ℝ)^b * ∑ q ∈ LatticeShells.box (n+3) (M/k), (LatticeShells.radius q)^c := by
    apply (measureReal_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ q ∈ LatticeShells.box (n+3) (M/k),
          A*(k : ℝ)^b*(LatticeShells.radius q)^c := by
        apply sum_le_sum
        intro q hq
        have hh := depthCell_sharp_volume n R C W q k hR hC hCR hW (Finset.mem_Icc.mp hk).1
        simpa [A,a,b,c,mul_assoc,mul_comm,mul_left_comm] using hh
      _ = _ := by rw [mul_sum]
  have hsum := LatticeShells.deep_weighted_sum (n+3) M (by omega)
  have he1 : ((n+3 : ℕ) : ℝ)-1 = (n : ℝ)+2 := by push_cast; ring
  have he2 : ((n+3 : ℕ) : ℝ)-5 = (n : ℝ)-2 := by push_cast; ring
  have he3 : ((n+3 : ℕ) : ℝ)+1 = (n : ℝ)+4 := by push_cast; ring
  have he4 : n+3-1 = n+2 := by omega
  rw [he1,he2,he3,he4] at hsum
  change volume.real (⋃ k ∈ Finset.Icc 1 M,
    ⋃ q ∈ LatticeShells.box (n+3) (M/k), depthCell (n+3) R W C q k) ≤ _
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 M,
        volume.real (⋃ q ∈ LatticeShells.box (n+3) (M/k), depthCell (n+3) R W C q k) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 M, A*(k : ℝ)^b*
        ∑ q ∈ LatticeShells.box (n+3) (M/k), (LatticeShells.radius q)^c :=
      sum_le_sum hkbound
    _ = A*∑ k ∈ Finset.Icc 1 M, (k : ℝ)^b*
        ∑ q ∈ LatticeShells.box (n+3) (M/k), (LatticeShells.radius q)^c := by
      rw [mul_sum]; apply sum_congr rfl; intro k hk; ring
    _ ≤ A*((4*(n+3)*3^(n+2) : ℕ)*(M : ℝ)^a) := mul_le_mul_of_nonneg_left hsum hA
    _ = _ := by dsimp [A,a,W,C,M]; ring


noncomputable def criticalHeight (n : ℕ) (R : ℝ) : ℝ :=
  R^(-(((n : ℝ)+2)/(n+4)))

noncomputable def deepCoefficient (n : ℕ) : ℝ :=
  cellCoefficient n (flatnessWidth (n+2)) (depthConstant (n+2))*
    (4*(n+3)*3^(n+2) : ℕ)*(depthConstant (n+2)+1)^(((n : ℝ)+2)/2)

theorem critical_depthRadius_le (n : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    (depthRadius (n+2) (criticalHeight n R) : ℝ) ≤
      (depthConstant (n+2)+1)*R^(((n : ℝ)+2)/(n+4)) := by
  let a := ((n : ℝ)+2)/(n+4)
  let C := depthConstant (n+2)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hC : 0 ≤ C := by dsimp [C,depthConstant,flatnessWidth]; positivity
  have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ C/(R^(-a)))
  rw [Real.rpow_neg hR0.le,div_eq_mul_inv,inv_inv] at hh
  have hp : 1 ≤ R^a := Real.one_le_rpow hR ha
  change (⌈C/(R^(-a))⌉₊ : ℝ) ≤ (C+1)*R^a
  rw [Real.rpow_neg hR0.le,div_eq_mul_inv,inv_inv]
  nlinarith

/-- The cell sum at the critical shallow/deep threshold has the sharp
missed-volume exponent d(d−1)/(d+1), with d=n+3. -/
theorem deepCells_critical_volume (n : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hCR : depthConstant (n+2) ≤ R) :
    volume.real (deepCells (n+2) R (criticalHeight n R)) ≤
      deepCoefficient n * R^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
  let a := ((n : ℝ)+2)/(n+4)
  let p := ((n : ℝ)+2)/2
  let C := depthConstant (n+2)
  let D := cellCoefficient n (flatnessWidth (n+2)) C
  let F : ℝ := (4*(n+3)*3^(n+2) : ℕ)
  let M := depthRadius (n+2) (criticalHeight n R)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hC : 0 ≤ C := by dsimp [C,depthConstant,flatnessWidth]; positivity
  have hD : 0 ≤ D := by dsimp [D,cellCoefficient,flatnessWidth]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hM : (M : ℝ) ≤ (C+1)*R^a := critical_depthRadius_le n R hR
  have hMp : (M : ℝ)^p ≤ ((C+1)*R^a)^p :=
    Real.rpow_le_rpow (by positivity) hM hp
  have he : R^p*(R^a)^p = R^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
    rw [← Real.rpow_mul hR0.le,← Real.rpow_add hR0]
    congr 1
    dsimp [p,a]
    field_simp
    ring
  have hb := deepCells_volume_bound n R (criticalHeight n R) hR0 hCR
  change volume.real (deepCells (n+2) R (criticalHeight n R)) ≤ D*R^p*F*(M : ℝ)^p at hb
  calc
    _ ≤ D*R^p*F*(M : ℝ)^p := hb
    _ ≤ D*R^p*F*(((C+1)*R^a)^p) :=
      mul_le_mul_of_nonneg_left hMp (by positivity)
    _ = (D*F*(C+1)^p)*(R^p*(R^a)^p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hR0.le _)]; ring
    _ = _ := by rw [he]; rfl

/-- Actual sharp-order missed-volume upper bound for every dimension at
least three. Every geometric, measure, flatness, grouping, and summation
input is proved in the preceding modules. -/
theorem exists_missed_volume_bound (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) R \ LatticeBody.body (n+3) R) ≤
        A*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  let D := deepCoefficient n
  let C := depthConstant (n+2)
  let A := (n+3 : ℕ)*V+D+1
  have hV : 0 ≤ V := measureReal_nonneg
  have hC : 0 ≤ C := by dsimp [C,depthConstant,flatnessWidth]; positivity
  have hD : 0 ≤ D := by dsimp [D,deepCoefficient,cellCoefficient,depthConstant,flatnessWidth]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨R₀,hR₀⟩ := exists_nat_gt (C+1)
  refine ⟨A,hA,R₀,?_⟩
  intro R hR
  have hRR : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hCR : C ≤ R := by linarith
  have hR0 : (0 : ℝ) < R := zero_lt_one.trans_le hR1
  let δ := criticalHeight n R
  have hδ : 0 < δ := Real.rpow_pos_of_pos hR0 _
  have hδR : δ ≤ R := by
    apply (Real.rpow_le_one_of_one_le_of_nonpos hR1 (neg_nonpos.mpr (by positivity))).trans hR1
  have hcover := missed_subset_shallow_union_deep (n+2) R δ hδ
  have hunion : volume (shallowCaps (n+3) R δ ∪ deepCells (n+2) R δ) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.union_subset
      ((shallowCaps_subset_annulus hδR).trans Set.sdiff_subset)
      (deepCells_subset_closedBall (n+2) R δ)) measure_closedBall_lt_top.ne
  have hm := measureReal_mono hcover hunion
  have hs0 := shallowCaps_critical_volume (n+2) R hR1
  have hs : volume.real (shallowCaps (n+3) R δ) ≤
      (n+3 : ℕ)*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4))*V := by
    simpa [δ,criticalHeight,V,Nat.cast_add,Nat.cast_ofNat,← neg_div,show n+2+1=n+3 by omega,show (n : ℝ)+2+2=n+4 by ring] using hs0
  have hd := deepCells_critical_volume n R hR1 hCR
  have hrpow : 0 ≤ (R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := Real.rpow_nonneg hR0.le _
  have hsum := (measureReal_union_le (μ := volume) (shallowCaps (n+3) R δ) (deepCells (n+2) R δ))
  change volume.real (deepCells (n+2) R δ) ≤ D*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) at hd
  dsimp [A]
  nlinarith [hm,hsum]

end LinearDistancePreservers.LatticeCaps

