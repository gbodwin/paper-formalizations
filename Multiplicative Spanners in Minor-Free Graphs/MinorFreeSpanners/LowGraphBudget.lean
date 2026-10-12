import MinorFreeSpanners.HeavyGraphBudget
import MinorFreeSpanners.NonnegativeWeightedGirth
import MinorFreeSpanners.GirthMinorFreeUpper

/-! Ordinary minor-free sparsity pays the low-weight edges from the same
canonical credit, using the literal unit spanning tree. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem low_graph_budget {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (ht : 4096≤t) (hr : 1≤r) (hh : 0<h)
    (hTree : T.IsTree) (hTpos : 0<T.edgeFinset.card)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) :
    (∑ e∈G.edgeFinset.filter (fun e => w e<(t:ℝ)),w e)≤
      canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  let sigma := fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ))
  have hL : 0≤fullDensityLoss h := by
    unfold fullDensityLoss densityPolylogLoss densityWitnessLoss
    positivity
  have hs : 0≤sigma := mul_nonneg hL (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hthreshold : ((2*r:ℕ):ℝ)≤2*(r:ℝ)*(1+2000/(t:ℝ)) := by
    push_cast
    have hd : (0:ℝ)≤2000/(t:ℝ) := by positivity
    nlinarith [(Nat.cast_nonneg r : (0:ℝ)≤r)]
  have hgsmall : WeightedGirthAbove G w (2*r:ℕ) := by
    intro a p hp e he
    exact (mul_le_mul_of_nonneg_right hthreshold (hw e (p.edges_subset_edgeSet he))).trans_lt
      (hG a p hp e he)
  have hcard := girth_minor_free_edge_bound G r h hr hh hfree
    (weightedGirth_girth_nonnegative hw hgsmall)
  have htreecard := hTree.card_edgeFinset
  have hn : (Fintype.card V:ℝ)≤2*(T.edgeFinset.card:ℝ) := by
    exact_mod_cast (show Fintype.card V≤2*T.edgeFinset.card by omega)
  have hc : (G.edgeFinset.card:ℝ)≤4*sigma*(T.edgeFinset.card:ℝ) := by
    have hb := mul_le_mul_of_nonneg_left hn (show 0≤2*sigma by positivity)
    dsimp [sigma] at hb ⊢
    nlinarith only [hcard,hb]
  have hsum : (∑ e∈G.edgeFinset.filter (fun e => w e<(t:ℝ)),w e)≤
      (t:ℝ)*(G.edgeFinset.card:ℝ) := by
    calc
      _ ≤ ∑ _e∈G.edgeFinset.filter (fun e => w e<(t:ℝ)),(t:ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        exact (Finset.mem_filter.mp he).2.le
      _ = (t:ℝ)*((G.edgeFinset.filter (fun e => w e<(t:ℝ))).card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_filter_le G.edgeFinset (fun e => w e<(t:ℝ))) (Nat.cast_nonneg _)
  have hcredit := (canonical_phase_credit t sigma (by omega)).2
  have hsmall : 4*sigma*(t:ℝ)≤canonicalPhaseCredit t r h := by
    change 4*sigma*(t:ℝ)≤30008*max 1 sigma*(t:ℝ)^3
    have hp : 0≤sigma*(t:ℝ) := mul_nonneg hs (Nat.cast_nonneg _)
    nlinarith only [hcredit,hp]
  have hb := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg t : (0:ℝ)≤t)
  have hp := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg T.edgeFinset.card)
  nlinarith only [hsum,hb,hp]

end MinorFreeSpanners
