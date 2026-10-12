import MinorFreeSpanners.HeavyStreamsBudget
import Mathlib.Data.Nat.Log

/-! The actual spanning-tree weight supplies the terminal cutoff. The number
of integer-start streams is fixed explicitly by the binary logarithm of t. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem heavy_graph_budget {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (ht : 4096≤t) (hr : 1≤r) (hh : 0<h)
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) :
    (∑ e∈G.edgeFinset.filter (fun e => (t:ℝ)≤w e),w e)≤
      42*(Nat.log 2 t+1:ℕ)*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  have ht1 : 1<t := by omega
  have hg := (canonical_phase_girth t r 1 ht hr le_rfl).1
  have hell : (t:ℝ)≤(2:ℝ)^(Nat.log 2 t+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) t).le
  have hcut : ∀ e∈G.edgeSet,w e<(t:ℝ)^(Nat.log t T.edgeFinset.card+1) := by
    intro e he
    have hupper := edge_weight_le_unit_spanning_budget hT hTree.connected hunit hg hG hw e he
    have hpow : (T.edgeFinset.card:ℝ)<(t:ℝ)^(Nat.log t T.edgeFinset.card+1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self ht1 T.edgeFinset.card
    exact hupper.trans_lt hpow
  exact heavy_edges_stream_budget t r h (Nat.log 2 t+1) (Nat.log t T.edgeFinset.card)
    ht hr hh hell hT hTree hunit hfree hG hw hcut

end MinorFreeSpanners
