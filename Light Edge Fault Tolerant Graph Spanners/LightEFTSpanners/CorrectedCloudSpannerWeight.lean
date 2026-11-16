import LightEFTSpanners.CorrectedCloudWeights
import LightEFTSpanners.CorrectedCloudRetention
import LightSpanners.TreeReduction

/-! Actual all-fault spanner semantics and the retained-bundle sum now give
one weight inequality, valid for every real stretch. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph LightSpanners Finset

/-- Positive MST-normalized clique weights are positive on every input edge. -/
theorem cloudWeight_positive {m p : ℕ} {G T : SimpleGraph (Fin m)}
    {w : Sym2 (Fin m) → ℝ} (hT : IsMinimumSpanningTree G T w)
    (hw : ∀ e∈G.edgeSet,0<w e) (hm : 2≤m) (hp : 0<p) :
    ∀ e∈(graph G p).edgeSet,0<cloudWeight T w p e := by
  have htree : 0<totalWeight T w := tree_totalWeight_pos hT.2.1
    (by simpa using hm) w (fun e he => hw e (edgeSet_mono hT.1 he))
  intro e he
  exact edgeWeight_pos hw (cloudDelta_pos (by omega) hp htree) he

/-- Every f-fault spanner of the corrected cloud graph retains the full
(f+1)-fold core weight. No stretch integrality assumption is used. -/
theorem cloud_spanner_weight_lower {m p f : ℕ} {G T : SimpleGraph (Fin m)}
    {H : SimpleGraph (Fin m × Fin p)} (w : Sym2 (Fin m) → ℝ) (t : ℝ)
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e∈G.edgeSet,0<w e)
    (hm : 2≤m) (hfp : f<p) (hg : WeightedGirthAbove G w (t+1))
    (hsp : IsEFTSpanner (graph G p) H (cloudWeight T w p) t f) :
    ((f:ℝ)+1)*totalWeight G w ≤ totalWeight H (cloudWeight T w p) := by
  have hp : 0<p := by omega
  have htree : 0<totalWeight T w := tree_totalWeight_pos hT.2.1
    (by simpa using hm) w (fun e he => hw e (edgeSet_mono hT.1 he))
  have hδ := (cloudDelta_pos (p:=p) (by omega) hp htree).le
  have hw0 : ∀ e∈G.edgeSet,0≤w e := fun e he => (hw e he).le
  have hW : ∀ e∈(graph G p).edgeSet,0≤cloudWeight T w p e :=
    fun e he => (cloudWeight_positive hT hw hm hp e he).le
  have hcross (a b : Fin m × Fin p) (hab : G.Adj a.1 b.1) :
      cloudWeight T w p s(a,b)=w s(a.1,b.1) := by
    simp only [cloudWeight,edgeWeight_pair,hab.ne,ite_false]
  have hret : ∀ e∈G.edgeSet,f+1≤(crossFiber H e).card := by
    intro e he
    rcases e with ⟨u,v⟩
    have huv := (mem_edgeSet G).mp he
    have hc := retainedBundle_card_gt w (cloudWeight T w p) t hw0 hW hcross hg hsp hfp huv
    change f+1≤(retainedBundle H u v).card
    omega
  have hh := retained_weight_lower hsp.1 w (cloudDelta T w p) hw0 hδ hret
  simpa only [Nat.cast_add,Nat.cast_one,cloudWeight] using hh

end LightEFTSpanners.CorrectedCloud
