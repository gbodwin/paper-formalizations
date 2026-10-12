import LightEFTSpanners.VotingGreedyCorrectness

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- The empirical-vote output on the actual weight-sorted non-seed edge list. -/
noncomputable def output (G Q : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J) (h : ℕ) :
    SimpleGraph V := edgeGraph (edges Q.edgeFinset w t eligible host tape h (input G Q w))

 theorem output_isEFTSpanner (G Q : SimpleGraph V) (hQ : Q≤G)
    (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (hf : 0<f) (ht : 1≤t) (hw : ∀ e,0≤w e)
    (hhost : ∀ e∈G.edgeFinset\Q.edgeFinset,∀ j∈eligible e,host j⊆Q.edgeFinset)
    (hcount : ∀ e∈G.edgeFinset\Q.edgeFinset,2*f+h≤(eligible e).card)
    (hcong : ∀ e∈G.edgeFinset\Q.edgeFinset,∀ d,(hosts (eligible e) host d).card≤2)
    (hacc : AccurateTrace Q.edgeFinset w t f eligible host tape h (input G Q w)) :
    IsEFTSpanner G (output G Q w t eligible host tape h) w t f := by
  have hgraph : edgeGraph (Q.edgeFinset∪(input G Q w).toFinset)=G := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [mem_edgeGraph,mem_union,List.mem_toFinset,mem_input,mem_edgeFinset]
    constructor
    · rintro ⟨he,_⟩
      rcases he with he | ⟨he,_⟩
      · exact SimpleGraph.edgeSet_mono hQ he
      · exact he
    · intro he
      refine ⟨?_,G.not_isDiag_of_mem_edgeSet he⟩
      by_cases heQ : e∈Q.edgeSet
      · exact Or.inl heQ
      · exact Or.inr ⟨he,heQ⟩
  have hin : ∀ e∈input G Q w,e∈G.edgeFinset\Q.edgeFinset := by
    intro e he
    exact mem_sdiff.mpr ((mem_input G Q w e).mp he)
  have h := edges_isEFTSpanner Q.edgeFinset w t f h eligible host tape hf ht hw
    (input G Q w) (fun e he => G.not_isDiag_of_mem_edgeFinset (mem_sdiff.mp (hin e he)).1)
    (fun e he => hhost e (hin e he)) (fun e he => hcount e (hin e he))
    (fun e he => hcong e (hin e he)) hacc
  simpa only [hgraph,output] using h
end LightEFTSpanners.SampledGreedy
