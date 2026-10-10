import LinearDistancePreservers.LatticeMinima
import Mathlib.Analysis.InnerProductSpace.Dual

namespace LinearDistancePreservers.LatticeMinima
open Module Set MeasureTheory
open scoped RealInnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Determinants of lattice vectors in a genuine integral lattice basis
are integers, including singular vector families. -/
theorem det_lattice_integer {d : ℕ} (B : Basis (Fin d) ℤ L)
    (v : Fin d → F) (hv : ∀ i, v i ∈ L) :
    ∃ k : ℤ, (B.ofZLatticeBasis ℝ).det v = (k : ℝ) := by
  let vZ : Fin d → L := fun i => ⟨v i,hv i⟩
  refine ⟨B.det vZ,?_⟩
  rw [Basis.det_apply,Basis.det_apply,Int.cast_det]
  congr 1
  ext i j
  exact B.ofZLatticeBasis_repr_apply ℝ L (vZ j) i

/-- Hadamard's inequality in any orthonormal coordinate basis. -/
theorem abs_orthonormal_det_le {d : ℕ} (e : OrthonormalBasis (Fin d) ℝ F) (v : Fin d → F) :
    |e.toBasis.det v| ≤ ∏ i, ‖v i‖ := by
  letI : Fact (Module.finrank ℝ F = d) := ⟨by simpa using Module.finrank_eq_card_basis e.toBasis⟩
  let o := e.toBasis.orientation
  have hh := o.abs_volumeForm_apply_le v
  rwa [o.volumeForm_robust' e v] at hh

/-- Euclidean covolume is the absolute determinant of an integral basis
in orthonormal coordinates. -/
theorem covolume_eq_abs_det {d : ℕ} (B : Basis (Fin d) ℤ L)
    (e : OrthonormalBasis (Fin d) ℝ F) :
    ZLattice.covolume L = |e.toBasis.det (B.ofZLatticeBasis ℝ)| := by
  have hvol : volume.real (ZSpan.fundamentalDomain e.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped e.toBasis volume)]
    change (volume (parallelepiped e)).toReal = 1
    rw [e.volume_parallelepiped,ENNReal.toReal_one]
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume B e.toBasis,hvol,mul_one]
  congr 2
  ext i
  simp

/-- The cofactor functional on the first d-1 independent lattice vectors
is a nonzero integral dual vector, with the sharp multiplicative norm bound.
No primitivity or basis-extension certificate is assumed. -/
theorem exists_integral_dual {n : ℕ} (B : Basis (Fin (n+1)) ℤ L)
    (b : Basis (Fin (n+1)) ℝ F) (hb : ∀ i, b i ∈ L)
    (e : OrthonormalBasis (Fin (n+1)) ℝ F) :
    ∃ q : F, q ≠ 0 ∧ (∀ z ∈ L, ∃ k : ℤ, inner ℝ q z = (k : ℝ)) ∧
      ‖q‖ ≤ (∏ i : Fin n, ‖b i.castSucc‖) / ZLattice.covolume L := by
  classical
  let BR := B.ofZLatticeBasis ℝ
  let f : F →ₗ[ℝ] ℝ := BR.det.toMultilinearMap.toLinearMap b (Fin.last n)
  let fc : F →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  let q := (InnerProductSpace.toDual ℝ F).symm fc
  have hq (x : F) : inner ℝ q x = f x := InnerProductSpace.toDual_symm_apply
  have hf (x : F) : f x = BR.det (Function.update b (Fin.last n) x) := rfl
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hBdet : BR.det b ≠ 0 := (BR.isUnit_det b).ne_zero
  have hqn : q ≠ 0 := by
    intro hzero
    have hh := hq (b (Fin.last n))
    rw [hzero,inner_zero_left,hf,Function.update_eq_self] at hh
    exact hBdet hh.symm
  have hint (z : F) (hz : z ∈ L) : ∃ k : ℤ, inner ℝ q z = (k : ℝ) := by
    rw [hq,hf]
    apply det_lattice_integer L B
    intro i
    by_cases hi : i = Fin.last n
    · subst i; simp [hz]
    · simpa [Function.update_of_ne hi] using hb i
  have hbound (x : F) : ‖f x‖ ≤
      ((∏ i : Fin n, ‖b i.castSucc‖) / ZLattice.covolume L) * ‖x‖ := by
    let v := Function.update b (Fin.last n) x
    have hdet : e.toBasis.det v = e.toBasis.det BR * BR.det v := by
      have hh := congrArg (fun a : F [⋀^Fin (n+1)]→ₗ[ℝ] ℝ => a v)
        (e.toBasis.det.eq_smul_basis_det BR)
      simpa using hh
    have hh := abs_orthonormal_det_le e v
    rw [hdet,abs_mul,← covolume_eq_abs_det L B e] at hh
    have hp : (∏ i, ‖v i‖) = (∏ i : Fin n, ‖b i.castSucc‖)*‖x‖ := by
      rw [Fin.prod_univ_castSucc]
      simp [v]
    rw [hp] at hh
    rw [Real.norm_eq_abs,hf]
    have he : |BR.det v| ≤ ((∏ i : Fin n, ‖b i.castSucc‖)*‖x‖) / ZLattice.covolume L :=
      (le_div_iff₀ hcov).mpr (by simpa [mul_comm] using hh)
    convert he using 1 <;> ring
  refine ⟨q,hqn,hint,?_⟩
  have he : ‖q‖ = ‖fc‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map fc
  rw [he]
  apply fc.opNorm_le_bound (by positivity)
  exact hbound

/-- Elementary Euclidean transference with an explicit dimension-only
constant. One integral dual vector works uniformly for every translate. -/
theorem exists_dual_covering {n : ℕ} (hdim : Module.finrank ℝ F = n+1) :
    ∃ q : F, q ≠ 0 ∧ (∀ z ∈ L, ∃ k : ℤ, inner ℝ q z = (k : ℝ)) ∧
      ∀ x : F, ∃ z ∈ L, dist x z * ‖q‖ ≤ ((n+1 : ℕ) : ℝ)^(n+2) := by
  classical
  obtain ⟨v,hv,hvL,hsmall⟩ := exists_minima_family L (IsZLattice.span_top (K := ℝ)) (n+1) (by omega)
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [hdim])
  have hbL : ∀ i, b i ∈ L := by simpa [b] using hvL
  have hbsmall : ∀ i, ∀ z ∈ L, ‖z‖ < ‖b i‖ → z ∈ Submodule.span ℝ (b '' Set.Iio i) := by
    simpa [b] using hsmall
  have hbmono := minima_norm_monotone L b hbL hbsmall
  obtain ⟨e,he⟩ := exists_minima_coordinates L b hbsmall
  have hprod := minima_product_le (by omega : 0 < n+1) L b e hbmono he
  have hindex : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n+1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,ZLattice.rank ℝ L,hdim]
  let B := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFinOfCardEq hindex)
  obtain ⟨q,hq,hqint,hqnorm⟩ := exists_integral_dual L B b hbL e
  have hcov := ZLattice.covolume_pos L volume
  have hlast : ‖q‖*‖b (Fin.last n)‖ ≤ ((n+1 : ℕ) : ℝ)^(n+1) := by
    calc
      _ ≤ ((∏ i : Fin n, ‖b i.castSucc‖) / ZLattice.covolume L)*‖b (Fin.last n)‖ :=
        mul_le_mul_of_nonneg_right hqnorm (norm_nonneg _)
      _ = (∏ i : Fin (n+1), ‖b i‖) / ZLattice.covolume L := by
        rw [Fin.prod_univ_castSucc]; ring
      _ ≤ _ := (div_le_iff₀ hcov).mpr hprod
  have hsum : (∑ i : Fin (n+1), ‖b i‖) ≤ (n+1 : ℕ)*‖b (Fin.last n)‖ := by
    calc
      _ ≤ ∑ _i : Fin (n+1), ‖b (Fin.last n)‖ :=
        Finset.sum_le_sum (fun i _ => hbmono (Fin.le_last i))
      _ = _ := by simp
  refine ⟨q,hq,hqint,?_⟩
  intro x
  obtain ⟨z,hz,hclose⟩ := exists_near_lattice L b hbL x
  refine ⟨z,hz,?_⟩
  calc
    _ ≤ ((n+1 : ℕ)*‖b (Fin.last n)‖)*‖q‖ :=
      mul_le_mul_of_nonneg_right (hclose.trans hsum) (norm_nonneg _)
    _ = (n+1 : ℕ)*(‖q‖*‖b (Fin.last n)‖) := by ring
    _ ≤ (n+1 : ℕ)*((n+1 : ℕ) : ℝ)^(n+1) :=
      mul_le_mul_of_nonneg_left hlast (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- A lattice-free translated open ball forces a bounded nonzero integral
dual direction, with no flatness or transference hypothesis. -/
theorem exists_short_dual_of_empty_ball {n : ℕ} (hdim : Module.finrank ℝ F = n+1)
    (x : F) {r : ℝ} (hr : 0 < r) (hempty : ∀ z ∈ L, r ≤ dist x z) :
    ∃ q : F, q ≠ 0 ∧ (∀ z ∈ L, ∃ k : ℤ, inner ℝ q z = (k : ℝ)) ∧
      ‖q‖ ≤ ((n+1 : ℕ) : ℝ)^(n+2) / r := by
  obtain ⟨q,hq,hint,hcover⟩ := exists_dual_covering L hdim
  obtain ⟨z,hz,hbound⟩ := hcover x
  refine ⟨q,hq,hint,(le_div_iff₀ hr).mpr ?_⟩
  have hh := mul_le_mul_of_nonneg_right (hempty z hz) (norm_nonneg q)
  nlinarith

end LinearDistancePreservers.LatticeMinima
