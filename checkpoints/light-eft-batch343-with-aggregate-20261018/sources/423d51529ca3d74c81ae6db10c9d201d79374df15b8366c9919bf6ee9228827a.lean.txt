import LightEFTSpanners.SubtreeCandidateAssignments

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

/-- Actual residual-blocker partition. Heavy candidates use cap r; light
candidates receive 2r+1 unblocked hosts and amortize the original cap f. -/
theorem subtree_heavy_light_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k r : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q≤G) (hQpos : 0<totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (j : ∀ i, A i ↪ V) (T : ∀ i, SimpleGraph (A i))
    (htrees : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,(T i).map (j i)≤Q)
    (hcount : ∀ e∈G.edgeFinset\Q.edgeFinset,
      2*f+1≤(indices.filter (fun i => ∃ d,(j i).sym2Map d=e)).card)
    (hcong : ∀ e∈Q.edgeFinset,(hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hr : 0<r) (hrf : r≤f) (hfr : f≤r*(2*r+1)) :
    totalWeight G w / totalWeight Q w ≤
      1+16*(r:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹)) := by
  classical
  let E := G.edgeFinset\Q.edgeFinset
  let heavy := E.filter (fun e => (B e\Q.edgeFinset).card≤r)
  let light := E.filter (fun e => ¬(B e\Q.edgeFinset).card≤r)
  let L : ℝ := 8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹)
  have hL : 0≤L := by dsimp [L];positivity
  have hh := candidate_packing_weight_bound (h:=1) (b:=f) hQG hB heavy
    (filter_subset _ _) indices j T htrees htreeQ
    (fun e he => hcount e (mem_filter.mp he).1)
    (fun e _ => (card_le_card inter_subset_left).trans (hB.capped e))
    (fun e he => (mem_filter.mp he).2) hcong hw hr hk heps
  have hs : ∀ e∈light,(B e∩Q.edgeFinset).card≤f-r := by
    intro e he
    have hres := (mem_filter.mp he).2
    have hc := hB.capped e
    have heq := card_inter_add_card_sdiff (B e) Q.edgeFinset
    omega
  have hl := candidate_packing_weight_bound (h:=2*r+1) (b:=f-r) hQG hB light
    (filter_subset _ _) indices j T htrees htreeQ
    (fun e he => by have hc:=hcount e (mem_filter.mp he).1;omega) hs
    (fun e _ => (card_le_card sdiff_subset).trans (hB.capped e)) hcong hw hf hk heps
  simp only [Nat.cast_one,one_mul] at hh
  change (∑ e∈heavy,w e)≤8*(r:ℝ)*L*totalWeight Q w at hh
  change ((2*r+1:ℕ):ℝ)*(∑ e∈light,w e)≤8*(f:ℝ)*L*totalWeight Q w at hl
  have hfrR : (f:ℝ)≤(r:ℝ)*(2*(r:ℝ)+1) := by exact_mod_cast hfr
  have hscale : 0≤8*L*totalWeight Q w := by positivity
  have hfscale := mul_le_mul_of_nonneg_right hfrR hscale
  have hlb : (∑ e∈light,w e)≤8*(r:ℝ)*L*totalWeight Q w := by
    push_cast at hl
    have hden : 0<2*(r:ℝ)+1 := by positivity
    nlinarith
  have hsum : (∑ e∈heavy,w e)+(∑ e∈light,w e)=∑ e∈E,w e := by
    exact sum_filter_add_sum_filter_not _ _ _
  have hweight : totalWeight G w=totalWeight Q w+∑ e∈E,w e := by
    unfold totalWeight
    have h := sum_sdiff (f:=w) (edgeFinset_mono hQG)
    dsimp [E]
    linarith
  apply (div_le_iff₀ hQpos).mpr
  rw [hweight]
  change totalWeight Q w+(∑ e∈E,w e)≤(1+16*(r:ℝ)*L)*totalWeight Q w
  nlinarith
end LightEFTSpanners
