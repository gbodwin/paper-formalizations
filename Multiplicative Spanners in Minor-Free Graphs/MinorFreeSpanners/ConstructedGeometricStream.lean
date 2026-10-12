import MinorFreeSpanners.CanonicalStreamBudget
import MinorFreeSpanners.InitialPrefixState

/-! A whole geometric weight stream is paid from the actual unit tree, with
neither an initial partition/credit state nor intermediate phase outputs supplied.
The last nonempty band itself certifies that the initial tree is large enough. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem constructed_geometric_stream_bound {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h b : ℕ) (ht : 4096≤t) (hb : 0<b) (hr : 1≤r) (hh : 0<h)
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) (n : ℕ)
    (hne : (weightBand G w ((t:ℝ)^(n+1)*(b:ℝ))
      (2*((t:ℝ)^(n+1)*(b:ℝ)))).edgeSet.Nonempty) :
    (∑ k∈range (n+1),∑ e∈(weightBand G w ((t:ℝ)^(k+1)*(b:ℝ))
      (2*((t:ℝ)^(k+1)*(b:ℝ)))).edgeFinset,w e)≤
        42*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  have hb1 : (1:ℝ)≤b := by exact_mod_cast hb
  have ht1 : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
  have hg := (canonical_phase_girth t r (b:ℝ) ht hr hb1).1
  have hc : 0≤canonicalPhaseCredit t r h := by unfold canonicalPhaseCredit;positivity
  have hsize : b≤T.edgeFinset.card := by
    obtain ⟨e,he⟩ := hne
    have hlow : (t:ℝ)^(n+1)*(b:ℝ)≤w e := by
      induction e using Sym2.inductionOn with
      | _ x y => exact he.2.1
    have hB : weightBand G w ((t:ℝ)^(n+1)*(b:ℝ))
        (2*((t:ℝ)^(n+1)*(b:ℝ)))≤G := fun _ _ hxy => hxy.1
    have hupper := edge_weight_le_unit_spanning_budget hT hTree.connected hunit hg hG hw e
      (edgeSet_mono hB he)
    have hp : 1≤(t:ℝ)^(n+1) := one_le_pow₀ ht1
    have hrsize : (b:ℝ)≤(T.edgeFinset.card:ℝ) := by nlinarith only [hp,hb1,hlow,hupper]
    exact_mod_cast hrsize
  obtain ⟨S0,hcredit⟩ := exists_initial_prefix_state hT hTree hunit b hb hsize
    (canonicalPhaseCredit t r h) hc
  exact canonical_stream_weight_bound t r h (b:ℝ) ht hb1 hr hh S0 hcredit
    hT hTree.connected hunit hfree hG hw n hne

end MinorFreeSpanners
