import MinorFreeSpanners.InitialBipartiteSelection
import MinorFreeSpanners.PostleBipartiteTrim

/-! Actual finite bipartite density increment. The initial regular graph,
full mate-free family, selected center set and cleaned quotient are all
constructed inside the proof. The parameter range is stated explicitly. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Every finite bipartite graph in this explicit domain has a genuinely
small dense induced subgraph or a positive bounded minor of increased density.
The hypotheses concern only the input graph, its two parts and parameters;
no packing, regularization, cleaning or minor certificate is assumed. -/
theorem bipartite_density_increment {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (ell d : ℕ) (k : ℝ)
    (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k) (hkd : k ≤ d)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hA : A.Nonempty)
    (hsize : ell*B.card ≤ A.card) (hdegree : ∀ x ∈ A, d ≤ G.degree x) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 10*k^3*d ∧
      0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (d:ℝ)/(400000*k^5)*S.card ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0 < n ∧ M.IsBounded (ell+1) ∧
      ((ell:ℝ)-1)*d*n ≤ (Q.edgeFinset.card:ℝ)) := by
  classical
  obtain ⟨H,hHG,hH,hreg,_hcard⟩ := exists_left_regular_subgraph G A B hG d hdegree
  obtain hs | hn := regular_bipartite_density_increment H A B ell d k hk hell hellk
    hkd hH hA hsize hreg
  · obtain ⟨S,hN,hE,hD⟩ := hs
    let f : (H.induce (S:Set V)) →g (G.induce (S:Set V)) := {
      toFun := id, map_rel' := fun h => hHG h }
    have hcount := hom_edge_count_le f Function.injective_id
    have hcountR : ((H.induce (S:Set V)).edgeFinset.card:ℝ) ≤
        (G.induce (S:Set V)).edgeFinset.card := by exact_mod_cast hcount
    exact Or.inl ⟨S,hN,hE.trans_le hcountR,hD.trans hcountR⟩
  · obtain ⟨n,Q,M,hpos,hM,hD⟩ := hn
    let f : H →g G := { toFun := id, map_rel' := fun h => hHG h }
    exact Or.inr ⟨n,Q,M.mapHost f Function.injective_id,hpos,
      MinorModel.IsBounded.mapHost M f Function.injective_id hM,hD⟩

end MinorFreeSpanners
