import MinorFreeSpanners.IntrinsicGirthGap
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Every edge in a graph of weighted girth at least two is bounded by
its unit-weight connected spanning subgraph's edge budget. In particular every
nonempty heavy band has upper scale at most twice the unit-tree weight. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

 theorem edge_weight_le_unit_spanning_budget {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ}
    (hT : T≤G) (hconn : T.Connected) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hg : 2≤g) (hG : WeightedGirthAbove G w g)
    (hw : ∀ e∈G.edgeSet,0≤w e) (e : Sym2 V) (he : e∈G.edgeSet) :
    w e≤(T.edgeFinset.card:ℝ) := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    by_cases hxy : T.Adj x y
    · rw [hunit _ hxy]
      have hp : 0<T.edgeFinset.card := Finset.card_pos.mpr ⟨s(x,y),by simpa using hxy⟩
      exact_mod_cast hp
    · obtain ⟨p⟩ := hconn.preconnected x y
      have hnot : s(x,y)∉(p.bypass.mapLe hT).edges := by
        intro hh
        have hh' : s(x,y)∈p.bypass.edges := by simpa using hh
        exact hxy (p.bypass.edges_subset_edgeSet hh')
      have hgap := replacement_walk_gap hG hw he (p.bypass.mapLe hT) hnot
      have hlen := p.bypass_isPath.isTrail.length_le_card_edgeFinset
      have hweight := walkWeight_eq_length_mul p.bypass w 1
        (fun f hf => hunit f (p.bypass.edges_subset_edgeSet hf))
      simp only [walkWeight_mapLe] at hgap
      rw [hweight,mul_one] at hgap
      have hnonneg := hw _ he
      have hstart : w s(x,y)≤(g-1)*w s(x,y) := by nlinarith only [hg,hnonneg]
      exact (hstart.trans hgap.le).trans (by exact_mod_cast hlen)

 theorem nonempty_band_scale_le_unit_budget {V : Type*} [Fintype V]
    {G T B : SimpleGraph V} {w : Sym2 V → ℝ} {g M : ℝ}
    (hT : T≤G) (hconn : T.Connected) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hg : 2≤g) (hG : WeightedGirthAbove G w g)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hB : B≤G)
    (hband : ∀ e∈B.edgeSet,M/2≤w e) (hne : B.edgeSet.Nonempty) :
    M≤2*(T.edgeFinset.card:ℝ) := by
  obtain ⟨e,he⟩ := hne
  have hupper := edge_weight_le_unit_spanning_budget hT hconn hunit hg hG hw e (edgeSet_mono hB he)
  have hlower := hband e he
  linarith

end MinorFreeSpanners
