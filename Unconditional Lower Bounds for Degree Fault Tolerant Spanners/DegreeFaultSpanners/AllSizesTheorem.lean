import DegreeFaultSpanners.PaperTheorem
import DegreeFaultSpanners.Padding
import DegreeFaultSpanners.DenseWitness
import DegreeFaultSpanners.AllSizesParameters
import DegreeFaultSpanners.AllSizesRealBound

/-!
# The lower bound for every admissible size

This file closes the prime-size and dense-parameter gaps. For every N>=2,
positive k, and 1<=f<=N, it constructs an N-vertex graph satisfying the
paper's real-exponent lower bound with the explicit constant 1/2^(k+3).
Prime proximity, isolated-vertex padding, and dense clique witnesses are
proved internally. The exact prime family retains its stronger constant1/4.
-/

namespace DegreeFaultSpanners

open SimpleGraph

/-- A finite graph on exactly N vertices with the explicit integer-power bound. -/
def HasAllSizesLowerBoundWitness (k f N : ℕ) : Prop :=
  ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
    letI : Fintype V := inst
    Fintype.card V = N ∧
      ∀ H : SimpleGraph V, IsDegreeFaultSpanner G H f (2 * k - 1) →
        f ^ (k - 1) * N ^ (k + 1) ≤
          allSizesFactor k ^ k * Nat.card H.edgeSet ^ k

/-- The dense regime uses actual bounded-degree clique components. -/
theorem all_sizes_dense_case (k f N : ℕ) (hk : 2 ≤ k) (hN : 2 ≤ N)
    (hf : 1 ≤ f) (hfN : f ≤ N) (hsmall : N ≤ 2 ^ (k + 1) * f) :
    HasAllSizesLowerBoundWitness k f N := by
  obtain ⟨V, inst, G, hcard, hdeg, hedges, hforce⟩ := exists_dense_all_N N f hN hf hfN
  letI : Fintype V := inst
  refine ⟨V, inst, G, hcard, ?_⟩
  intro H hH
  have hHG : H = G := hforce (2 * k - 1) H hH
  rw [hHG]
  exact dense_parameter_power_lower_bound k f N (Nat.card G.edgeSet) hk hsmall hedges

/-- In the large regime, a proved nearby prime supplies a forcing graph which is padded to N. -/
theorem all_sizes_large_case (k f N : ℕ) (hk : 2 ≤ k) (hf : 1 ≤ f)
    (hlarge : 2 ^ (k + 1) * f ≤ N) : HasAllSizesLowerBoundWitness k f N := by
  classical
  obtain ⟨p, hp, hfit, hnear⟩ := exists_prime_family_fit k f N hk hf hlarge
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let V := Vertex (ZMod p) (k - 2) × Fin f
  let G : SimpleGraph V := paperGraph (F := ZMod p) k f
  letI : Nonempty V := ⟨(Sum.inl 0, ⟨0, by omega⟩)⟩
  have hcounts := paperGraph_counts (F := ZMod p) k f hk
  simp only [ZMod.card] at hcounts
  have hcard : Fintype.card V ≤ N := by
    change Fintype.card (Vertex (ZMod p) (k - 2) × Fin f) ≤ N
    rw [hcounts.1]
    exact hfit
  have hforce : ∀ H : SimpleGraph V,
      IsDegreeFaultSpanner G H f (2 * k - 1) → H = G := by
    intro H hH
    exact paperGraph_spanner_eq (F := ZMod p) k f hk hH
  obtain ⟨G', hG'card, hG'force⟩ := exists_padded_forcing_graph G hcard hforce
  refine ⟨Fin N, inferInstance, G', Fintype.card_fin N, ?_⟩
  intro H hH
  rw [hG'force H hH, hG'card]
  change f ^ (k - 1) * N ^ (k + 1) ≤
    allSizesFactor k ^ k * Nat.card (paperGraph (F := ZMod p) k f).edgeSet ^ k
  rw [hcounts.2]
  exact family_padding_power_lower_bound k p f N hk hnear

/-- The repaired dimension-one case works at every size, with every fault budget. -/
theorem all_sizes_k_one_case (f N : ℕ) (hN : 2 ≤ N) :
    HasAllSizesLowerBoundWitness 1 f N := by
  classical
  refine ⟨Fin N, inferInstance, ⊤, Fintype.card_fin N, ?_⟩
  intro H hH
  have hcard : Nat.card H.edgeSet = N.choose 2 := by
    have h := complete_one_spanner_edge_count (f := f) hH
    simpa only [Nat.card_coe_set_eq, Fintype.card_fin] using h
  have hsmall : N ^ 2 ≤ 4 * N.choose 2 := complete_graph_quadratic_lower_bound N hN
  have hbig : N ^ 2 ≤ 16 * N.choose 2 :=
    hsmall.trans (Nat.mul_le_mul_right (N.choose 2) (by decide : 4 ≤ 16))
  norm_num only [allSizesFactor, hcard, Nat.sub_self, pow_zero, one_mul, pow_one]
  exact hbig

/-- Complete all-N integer-power version, including the dense regime and k=1. -/
theorem theorem_five_all_sizes_power (k f N : ℕ)
    (hk : 1 ≤ k) (hN : 2 ≤ N) (hf : 1 ≤ f) (hfN : f ≤ N) :
    HasAllSizesLowerBoundWitness k f N := by
  by_cases hk1 : k = 1
  · subst k
    exact all_sizes_k_one_case f N hN
  · have hk2 : 2 ≤ k := by omega
    by_cases hlarge : 2 ^ (k + 1) * f ≤ N
    · exact all_sizes_large_case k f N hk2 hf hlarge
    · exact all_sizes_dense_case k f N hk2 hN hf hfN (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))

/-- Theorem 5 for every N>=2 and 1<=f<=N, with real exponents and a proved explicit constant.
No prime proximity, padding, dense graph, or geometric premise remains in this statement. -/
theorem theorem_five_all_sizes (k f N : ℕ)
    (hk : 1 ≤ k) (hN : 2 ≤ N) (hf : 1 ≤ f) (hfN : f ≤ N) :
    ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
      letI : Fintype V := inst
      Fintype.card V = N ∧
        ∀ H : SimpleGraph V, IsDegreeFaultSpanner G H f (2 * k - 1) →
          (1 / (allSizesFactor k : ℝ)) * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
            (N : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (Nat.card H.edgeSet : ℝ) := by
  obtain ⟨V, inst, G, hcard, hbound⟩ := theorem_five_all_sizes_power k f N hk hN hf hfN
  letI : Fintype V := inst
  refine ⟨V, inst, G, hcard, ?_⟩
  intro H hH
  exact real_lower_bound_of_power_factor k f N (Nat.card H.edgeSet) (allSizesFactor k)
    hk (by simp [allSizesFactor]) (hbound H hH)

/-- Fully quantified asymptotic contract: the positive constant depends only on k,
not on the independently chosen graph size N or fault budget f. -/
theorem theorem_five_uniform_parameters (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N f : ℕ), 2 ≤ N → 1 ≤ f → f ≤ N →
      ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
        letI : Fintype V := inst
        Fintype.card V = N ∧
          ∀ H : SimpleGraph V, IsDegreeFaultSpanner G H f (2 * k - 1) →
            c * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
              (N : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (Nat.card H.edgeSet : ℝ) := by
  refine ⟨1 / (allSizesFactor k : ℝ), ?_, ?_⟩
  · have hpos : 0 < allSizesFactor k := by simp [allSizesFactor]
    exact one_div_pos.mpr (by exact_mod_cast hpos)
  · intro N f hN hf hfN
    exact theorem_five_all_sizes k f N hk hN hf hfN

end DegreeFaultSpanners
