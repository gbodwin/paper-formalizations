import LightSpanners.EndpointCounting
import LightSpanners.RetainedGraph
import LightSpanners.ChordPrefix

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Medium counting on every selected chord set, using actual retained graphs,
exact extra-safe truncation, useful families and dispersion under deletion. -/
theorem medium_counting (S : Finset (Sym2 V))
    (hS : ∀ e∈S,e∈G.edgeSet ∧ e∉C.cycle.edges)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    eps/4*(∑ e∈S,w e)-(Fintype.card V:ℝ)≤(C.safeEndpoints eps k S).card := by
  revert hS
  refine Finset.strongInductionOn S ?_
  intro S ih hS
  by_cases hweight : 4/eps*(Fintype.card V:ℝ)≤∑ e∈S,w e
  · obtain ⟨u,v,p,⟨J,hp⟩,hcount,hsupport⟩ := C.weak_counting_retained S hS heps hk hweight
    obtain ⟨z,q,J',_,hq,hqcount,hprefix⟩ := hp.truncate C hk hcount
    have hqS : ∀ e∈C.chordEdges q,e∈S := by
      intro e he
      exact hsupport e (hprefix.sublist.subset he)
    obtain ⟨e,es,N,f,hword,hf,hN,hpaths⟩ := C.useful_family heps hk hG ⟨hqcount,J',hq⟩
    have heS : e∈S := hqS e (by simp [hword])
    have hgain := C.erase_chord_endpoint_gain (S:=S) (e:=e) heps hk hG f hf (by
      intro a
      obtain ⟨r,hr,hrword⟩ := hpaths a
      exact ⟨r,hr,by simp [hrword,hword],fun d hd => hqS d (by rwa [← hrword])⟩)
    have hi := ih (S.erase e) (Finset.erase_ssubset heS)
      (fun d hd => hS d (Finset.mem_of_mem_erase hd))
    have hsum : (∑ d∈S.erase e,w d)+w e=∑ d∈S,w d := Finset.sum_erase_add S w heS
    have hgainR : ((C.safeEndpoints eps k (S.erase e)).card:ℝ)+N≤
        (C.safeEndpoints eps k S).card := by exact_mod_cast hgain
    nlinarith
  · have hsmall : eps/4*(∑ e∈S,w e)≤(Fintype.card V:ℝ) := by
      have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hweight) heps
      have hcancel : eps*(4/eps*(Fintype.card V:ℝ))=4*Fintype.card V := by field_simp
      rw [hcancel] at hh
      linarith
    have hn : (0:ℝ)≤(C.safeEndpoints eps k S).card := by positivity
    linarith

end LightSpanners.UnitSpanningCycle
