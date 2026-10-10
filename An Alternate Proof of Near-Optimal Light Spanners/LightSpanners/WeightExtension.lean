import LightSpanners.MainTheorem

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weights away from actual graph edges are immaterial to every walk weight. -/
theorem walkWeight_congr_on_edges {G : SimpleGraph V} {w w' : Sym2 V → ℝ}
    (heq : ∀ e∈G.edgeSet,w e=w' e) {u v : V} (p : G.Walk u v) :
    walkWeight w p=walkWeight w' p := by
  unfold walkWeight
  congr 1
  exact List.map_congr_left (fun e he => heq e (p.edges_subset_edgeSet he))

theorem totalWeight_congr_on_edges {G : SimpleGraph V} {w w' : Sym2 V → ℝ}
    (heq : ∀ e∈G.edgeSet,w e=w' e) : totalWeight G w=totalWeight G w' := by
  apply Finset.sum_congr rfl
  intro e he
  exact heq e (by simpa using he)

/-- The existence statement needs positivity only on graph edges. The harmless
nonnegative extension off the graph is constructed internally. -/
theorem exists_near_optimal_spanner (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hconn : G.Connected) (hw : ∀ e∈G.edgeSet,0<w e)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k) :
    ∃ H T : SimpleGraph V,
      IsSpanner G H w ((1+eps)*(2*k-1)) ∧ IsMinimumSpanningTree G T w ∧
      (∀ u v, weightedDistance H w u v≤
        ENNReal.ofReal ((1+eps)*(2*k-1))*weightedDistance G w u v) ∧
      lightness H T w≤(8+2048/eps)*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  let w' : Sym2 V → ℝ := fun e => max (w e) 0
  have hw0' : ∀ e,0≤w' e := fun e => le_max_right _ _
  have heq : ∀ e∈G.edgeSet,w' e=w e := fun e he => max_eq_left (hw e he).le
  have hw' : ∀ e∈G.edgeSet,0<w' e := fun e he => by rw [heq e he]; exact hw e he
  let H := greedyOutput G w' ((1+eps)*(2*k-1))
  obtain ⟨hspan,_,T,hT,hTH,hlight⟩ := near_optimal_greedy_spanner G w' hconn hw0' hw' heps hk
  have hspan' : IsSpanner G H w ((1+eps)*(2*k-1)) := by
    refine ⟨hspan.1,?_⟩
    intro u v p
    obtain ⟨q,hq⟩ := hspan.2 u v p
    rw [walkWeight_congr_on_edges heq p,
      walkWeight_congr_on_edges (fun e he => heq e (edgeSet_mono hspan.1 he)) q] at hq
    exact ⟨q,hq⟩
  have hT' : IsMinimumSpanningTree G T w := by
    refine ⟨hT.1,hT.2.1,?_⟩
    intro S hS htree
    have hh := hT.2.2 S hS htree
    rwa [totalWeight_congr_on_edges (fun e he => heq e (edgeSet_mono hT.1 he)),
      totalWeight_congr_on_edges (fun e he => heq e (edgeSet_mono hS he))] at hh
  have ht : 0<(1+eps)*(2*(k:ℝ)-1) := by
    have hkR : (1:ℝ)≤k := by exact_mod_cast hk
    have hterm : (0:ℝ)<2*(k:ℝ)-1 := by linarith
    positivity
  have hlight' : lightness H T w≤8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
    change lightness H T w'≤_ at hlight
    unfold lightness at hlight ⊢
    rwa [totalWeight_congr_on_edges (fun e he => heq e (edgeSet_mono hspan.1 he)),
      totalWeight_congr_on_edges (fun e he => heq e (edgeSet_mono hT.1 he))] at hlight
  haveI := hconn.nonempty
  have hn : (1:ℝ)≤Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hroot := Real.one_le_rpow hn (show (0:ℝ)≤(k:ℝ)⁻¹ by positivity)
  exact ⟨H,T,hspan',hT',hspan'.distance_le ht,by nlinarith⟩

end LightSpanners
