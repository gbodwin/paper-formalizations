import LightSpanners.DyadicEnumeration
import LightSpanners.TourCycle
import Mathlib.Analysis.Real.Sqrt

namespace LightSpanners
open SimpleGraph Finset

/-- The unit Hamiltonian cycle alone contributes its number of vertices. -/
theorem UnitSpanningCycle.card_le_totalWeight {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w) :
    (Fintype.card V : ℝ) ≤ totalWeight G w := by
  classical
  have hn : (0:ℝ) ≤ ∑ e ∈ G.edgeFinset with e ∉ C.cycle.edges, w e := by
    apply Finset.sum_nonneg
    intro e he
    exact le_trans zero_le_one (C.lower e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1))
  rw [C.noncycle_weight] at hn
  linarith

/-- Literal uniform all-epsilon dependence in Theorem 5.1 needs the additive
unit-cycle term (or an upper bound on epsilon). For every proposed constant,
an actual canonical unit cycle with k=2 violates that uniform estimate. -/
theorem no_uniform_all_epsilon_bound (A : ℝ) (_hA : 0≤A) :
    ∃ (n : ℕ) (eps : ℝ), 0<eps ∧
      WeightedGirthAbove (cycleGraph (n+3)) (fun _ => 1) ((1+4*eps)*4) ∧
      A*(n+3:ℝ)*Real.sqrt (n+3) < eps*totalWeight (cycleGraph (n+3)) (fun _ => 1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max (3:ℝ) (32*A))
  have hm3 : 3 < (m:ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmA : 32*A < (m:ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmn : 3≤m := by exact_mod_cast hm3.le
  have hmsq : 3≤m^2 := by nlinarith
  let n := m^2-3
  have hn : n+3=m^2 := Nat.sub_add_cancel hmsq
  have hnR : (n:ℝ)+3=(m:ℝ)^2 := by exact_mod_cast hn
  let eps : ℝ := ((n:ℝ)+3)/32
  have heps : 0<eps := by dsimp [eps]; positivity
  have hweight := (canonicalUnitSpanningCycle n).card_le_totalWeight
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hweight
  have hsqrt : Real.sqrt ((n:ℝ)+3)=(m:ℝ) := by
    rw [hnR,Real.sqrt_sq (Nat.cast_nonneg m)]
  refine ⟨n,eps,heps,cycleGraph_weightedGirthAbove ?_,?_⟩
  · dsimp [eps]
    nlinarith [sq_nonneg ((m:ℝ)-3)]
  · rw [hsqrt]
    have hmul := mul_le_mul_of_nonneg_left hweight heps.le
    have hpos : 0 < ((m:ℝ)^3) := by positivity
    have hstrict := mul_lt_mul_of_pos_right hmA hpos
    dsimp only [eps] at hmul ⊢
    rw [hnR] at hmul ⊢
    nlinarith

end LightSpanners

namespace LightSpanners
/-- The same unit-cycle family also rules out a finite constant uniform in
all positive epsilon in the warmup Theorem 4.1, already at k=2. -/
theorem no_uniform_warmup_epsilon_bound (A : ℝ) (hA : 0≤A) :
    ∃ (n : ℕ) (eps : ℝ), 0<eps ∧
      WeightedGirthAbove (SimpleGraph.cycleGraph (n+3)) (fun _ => (1:ℝ)) ((1+2*eps)*4) ∧
      A*2*(n+3)*Real.sqrt (n+3)<eps*totalWeight (SimpleGraph.cycleGraph (n+3)) (fun _ => (1:ℝ)) := by
  obtain ⟨n,eps,heps,hg,hbound⟩ := no_uniform_all_epsilon_bound A hA
  refine ⟨n,2*eps,by positivity,?_,?_⟩
  · convert hg using 1 <;> ring
  · nlinarith
end LightSpanners
