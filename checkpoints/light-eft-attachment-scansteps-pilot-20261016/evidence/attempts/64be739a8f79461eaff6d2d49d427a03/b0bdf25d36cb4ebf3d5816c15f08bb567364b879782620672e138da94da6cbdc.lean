import LightEFTSpanners.EmpiricalVotingGreedy
import LightEFTSpanners.HostCounting

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V J : Type*} [DecidableEq V] [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- Every actual fault witness forces h accurate hosts to vote. The bound uses
original fault identities, congestion two and the exact finite Bernoulli law. -/
theorem fault_witness_forces_votes (Q E : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f h : ℕ) (eligible : Sym2 V → Finset J)
    (host : J → Finset (Sym2 V)) (tape : Tape V J) (e : Sym2 V)
    (hf : 0<f) (hQE : Q⊆E)
    (hhost : ∀ j∈eligible e,host j⊆Q)
    (hcount : 2*f+h≤(eligible e).card)
    (hcong : ∀ d,(hosts (eligible e) host d).card≤2)
    (hacc : ∀ j∈eligible e,|estimate Q E (host j) w t e (tape E e j)-
      testProbability Q E (host j) w t f e|≤1/8)
    (hbad : ¬FTCovered (edgeGraph E) w t f e) :
    h≤(votes Q w t eligible host tape E e).card := by
  classical
  simp only [FTCovered,not_forall] at hbad
  obtain ⟨F,hF,_,hbadF⟩ := hbad
  have hh := two_congestion_hosts (eligible e) host F f h hcount hF (fun d _ => hcong d)
  apply hh.trans
  apply card_le_card
  intro j hj
  obtain ⟨hj,hdis⟩ := mem_filter.mp hj
  apply mem_filter.mpr
  refine ⟨hj,?_⟩
  apply BlockerSampling.accepts_required_edge
  · exact fault_witness_testProbability Q E (host j) F w t f e hf hF
      ((hhost j hj).trans hQE) hdis hbadF
  · exact hacc j hj
end LightEFTSpanners.SampledGreedy
