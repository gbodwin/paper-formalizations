import LightEFTSpanners.SamplingFaultAvoidance
import LightEFTSpanners.SeededGreedy

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners LightSpanners.FiniteSampling
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A literal sampled current graph: retain the host deterministically and
only sampled non-seed current edges. Clipping makes every finite tape valid. -/
noncomputable def testSample (Q E T S : Finset (Sym2 V)) : SimpleGraph V :=
  edgeGraph (T∪(S∩(E\Q)))

/-- True probability is a finite sum over all actual Bernoulli subgraphs. -/
noncomputable def testProbability (Q E T : Finset (Sym2 V))
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (e : Sym2 V) : ℝ :=
  ∑ S∈(E\Q).powerset with ¬Covered (testSample Q E T S) w t e,
    mass (E\Q) (1/(2*(f:ℝ))) S

/-- Every sampled graph omitting the witness faults lies in the actual
post-fault current graph, as long as its deterministic host avoids them. -/
theorem testSample_le_afterFaults (Q E T S F : Finset (Sym2 V))
    (hTE : T⊆E) (hTF : Disjoint T F) (hSF : Disjoint S F) :
    testSample Q E T S≤afterFaults (edgeGraph E) F := by
  intro a b hab
  obtain ⟨hh,hn⟩ := (mem_edgeGraph (T∪(S∩(E\Q))) s(a,b)).mp hab
  apply (mem_afterFaults (edgeGraph E) F s(a,b)).mpr
  rcases mem_union.mp hh with hh | hh
  · exact ⟨(mem_edgeGraph _ _).mpr ⟨hTE hh,hn⟩,fun he => disjoint_left.mp hTF hh he⟩
  · obtain ⟨hS,hEQ⟩ := mem_inter.mp hh
    exact ⟨(mem_edgeGraph _ _).mpr ⟨(mem_sdiff.mp hEQ).1,hn⟩,fun he => disjoint_left.mp hSF hS he⟩

/-- An actual fault witness forces true rejection probability at least1/2.
No probability oracle or desired statistical inequality is assumed. -/
theorem fault_witness_testProbability (Q E T F : Finset (Sym2 V))
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (e : Sym2 V)
    (hf : 0<f) (hF : F.card≤f) (hTE : T⊆E) (hTF : Disjoint T F)
    (hbad : ¬Covered (afterFaults (edgeGraph E) F) w t e) :
    1/2≤testProbability Q E T w t f e := by
  have hbase := BlockerSampling.corrected_fault_avoidance (E\Q) F f hf hF
  have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
  have hp1 : 1/(2*(f:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
  apply hbase.trans
  unfold testProbability
  apply sum_le_sum_of_subset_of_nonneg
  · intro S hS
    obtain ⟨hS,hd⟩ := mem_filter.mp hS
    refine mem_filter.mpr ⟨hS,?_⟩
    exact fun hc => hbad (covered_mono (testSample_le_afterFaults Q E T S F hTE hTF hd) hc)
  · intro S _ _
    exact mass_nonneg _ _ (by positivity) hp1
end LightEFTSpanners
