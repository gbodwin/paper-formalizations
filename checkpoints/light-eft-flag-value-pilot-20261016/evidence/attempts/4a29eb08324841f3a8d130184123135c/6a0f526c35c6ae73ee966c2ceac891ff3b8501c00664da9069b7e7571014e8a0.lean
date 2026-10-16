import LightEFTSpanners.VotingFaultWitness

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting
variable {V J : Type*} [DecidableEq V] [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- Conditional correctness of the literal empirical-vote execution. The only
statistical premise is accuracy on its actual queried states; all needed host
votes are derived from fault witnesses, not assumed acceptance behavior. -/
theorem edges_covered (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f h : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (tape : Tape V J) (hf : 0<f) (ht : 1≤t) (hw : ∀ e,0≤w e)
    (l : List (Sym2 V)) (hl : ∀ e∈l,¬e.IsDiag)
    (hhost : ∀ e∈l,∀ j∈eligible e,host j⊆Q)
    (hcount : ∀ e∈l,2*f+h≤(eligible e).card)
    (hcong : ∀ e∈l,∀ d,(hosts (eligible e) host d).card≤2)
    (hacc : AccurateTrace Q w t f eligible host tape h l) :
    ∀ e∈l,FTCovered (edgeGraph (edges Q w t eligible host tape h l)) w t f e := by
  induction l with
  | nil => simp
  | cons e es ih =>
    obtain ⟨hprev,hcur⟩ := hacc
    have htail (d) (hd : d∈es) : d∈e::es := List.mem_cons_of_mem e hd
    have hi := ih (fun d hd => hl d (htail d hd))
      (fun d hd => hhost d (htail d hd)) (fun d hd => hcount d (htail d hd))
      (fun d hd => hcong d (htail d hd)) hprev
    intro d hd
    simp only [edges]
    split_ifs with hvote
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact ftCovered_of_mem ht hw ((mem_edgeGraph _ _).mpr
          ⟨mem_insert_self _ _,hl d (by simp)⟩)
      · exact ftCovered_mono (edgeGraph_mono (subset_insert _ _)) (hi d hd)
    · rcases List.mem_cons.mp hd with rfl | hd
      · by_contra hb
        exact hvote (fault_witness_forces_votes Q (edges Q w t eligible host tape h es)
          w t f h eligible host tape d hf (seed_subset Q w t eligible host tape h es)
          (hhost d (by simp)) (hcount d (by simp)) (hcong d (by simp)) hcur hb)
      · exact hi d hd

 theorem edges_isEFTSpanner (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f h : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (tape : Tape V J) (hf : 0<f) (ht : 1≤t) (hw : ∀ e,0≤w e)
    (l : List (Sym2 V)) (hl : ∀ e∈l,¬e.IsDiag)
    (hhost : ∀ e∈l,∀ j∈eligible e,host j⊆Q)
    (hcount : ∀ e∈l,2*f+h≤(eligible e).card)
    (hcong : ∀ e∈l,∀ d,(hosts (eligible e) host d).card≤2)
    (hacc : AccurateTrace Q w t f eligible host tape h l) :
    IsEFTSpanner (edgeGraph (Q∪l.toFinset))
      (edgeGraph (edges Q w t eligible host tape h l)) w t f := by
  apply ftCovered_edges_spanner (edgeGraph_mono (subset_input Q w t eligible host tape h l))
  intro e he
  obtain ⟨he,hn⟩ := (mem_edgeGraph _ _).mp he
  rcases mem_union.mp he with he | he
  · exact ftCovered_of_mem ht hw ((mem_edgeGraph _ _).mpr
      ⟨seed_subset Q w t eligible host tape h l he,hn⟩)
  · exact edges_covered Q w t f h eligible host tape hf ht hw l hl hhost hcount hcong hacc
      e (List.mem_toFinset.mp he)
end LightEFTSpanners.SampledGreedy
