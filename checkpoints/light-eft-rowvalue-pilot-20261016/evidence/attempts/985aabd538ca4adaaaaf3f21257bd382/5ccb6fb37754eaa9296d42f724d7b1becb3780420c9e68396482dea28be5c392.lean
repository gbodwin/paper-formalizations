import LightEFTSpanners.SampledHistoryCandidates

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners LightSpanners.FiniteSampling
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The true estimator law at a compressed admission prefix is exactly the
law of that prefix's original edge identities. -/
theorem testProbability_prefix (Q R T : Finset (Sym2 V))
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (e : Sym2 V) (hdis : Disjoint R Q) :
    testProbability Q (Q∪R) T w t f e=
      ∑ S∈R.powerset,mass R (1/(2*(f:ℝ))) S*
        (if ¬Covered (edgeGraph (T∪S)) w t e then 1 else 0) := by
  have hR : (Q∪R)\Q=R := by
    ext d
    have hd : d∈R → d∉Q := fun hr hq => disjoint_left.mp hdis hr hq
    simp only [mem_sdiff,mem_union]
    tauto
  unfold testProbability
  rw [hR,sum_filter]
  apply sum_congr rfl
  intro S hS
  have hS' := mem_powerset.mp hS
  have htS : testSample Q (Q∪R) T S=edgeGraph (T∪S) := by
    unfold testSample
    rw [hR,inter_eq_left.mpr hS']
  rw [htS]
  split_ifs <;> ring

/-- A fresh actual sample that fails against the entire execution prefix also
fails against the smaller greedily retained host prefix. -/
theorem sampled_prefix_rejection_probability (Q T : Finset (Sym2 V))
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (j : J)
    (rs : List (Sym2 V × Finset J)) (e : Sym2 V) (hf : 0<f)
    (hdis : ∀ d∈rs.map Prod.fst,d∉Q) :
    testProbability Q (Q∪(rs.map Prod.fst).toFinset) T w t f e≤
      ∑ S∈(rs.map Prod.fst).toFinset.powerset,
        mass (rs.map Prod.fst).toFinset (1/(2*(f:ℝ))) S*
          (if ¬FTCovered (edgeGraph (greedyEdges T w t 0 (selectedList j S rs))) w t 0 e
            then 1 else 0) := by
  classical
  have hD : Disjoint (rs.map Prod.fst).toFinset Q := disjoint_left.mpr
    (fun d hd => hdis d (List.mem_toFinset.mp hd))
  rw [testProbability_prefix Q _ T w t f e hD]
  have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
  have hp1 : 1/(2*(f:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
  apply sum_le_sum
  intro S hS
  have hm := mass_nonneg (rs.map Prod.fst).toFinset S (by positivity) hp1
  by_cases hb : ¬Covered (edgeGraph (T∪S)) w t e
  · have hn : ¬FTCovered (edgeGraph (greedyEdges T w t 0 (selectedList j S rs))) w t 0 e := by
      intro hc
      have hmono : edgeGraph (greedyEdges T w t 0 (selectedList j S rs))≤edgeGraph (T∪S) := by
        apply edgeGraph_mono
        intro d hd
        rcases mem_union.mp (greedy_subset T w t 0 _ hd) with hd | hd
        · exact mem_union_left _ hd
        · exact mem_union_right _ (selectedList_mem_sample j S rs (List.mem_toFinset.mp hd))
      exact hb (covered_mono hmono ((ftCovered_zero _ _ _ _).mp hc))
    simp [hb,hn]
  · simp only [hb,ite_false,mul_zero]
    split_ifs <;> simp_all
end LightEFTSpanners.SampledGreedy
