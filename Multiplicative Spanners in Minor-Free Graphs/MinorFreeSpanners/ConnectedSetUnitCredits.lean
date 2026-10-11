import MinorFreeSpanners.InitialConnectedPartition
import MinorFreeSpanners.ClusterGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual internal original-edge budgets and intrinsic unit-weight paths. -/
namespace MinorFreeSpanners
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

noncomputable def internalEdges {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => e.toFinset ⊆ S

 theorem ConnectedWithin.induce_connected {V : Type*} {G : SimpleGraph V}
    {S : Finset V} (hS : ConnectedWithin G S) (hne : S.Nonempty) :
    (G.induce (S:Set V)).Connected := by
  obtain ⟨x,hx⟩ := hne
  let : Nonempty (S:Set V) := ⟨⟨x,hx⟩⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨p,hp⟩ := hS a.val a.property b.val b.property
  exact ⟨p.induce (S:Set V) hp⟩

 theorem internalEdges_card_lower {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (hS : ConnectedWithin G S)
    (hne : S.Nonempty) : S.card-1 ≤ (internalEdges G S).card := by
  classical
  have h := (hS.induce_connected hne).card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h
  simp only [← Set.toFinset_card,Finset.toFinset_coe] at h
  have he := G.card_filter_edgeFinset_toFinset_subset S
  change (internalEdges G S).card = _ at he
  omega

 theorem internalEdges_disjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) {S T : Finset V} (hST : Disjoint S T) :
    Disjoint (internalEdges G S) (internalEdges G T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hs ht
  have hs' := (Finset.mem_filter.mp hs).2
  have ht' := (Finset.mem_filter.mp ht).2
  induction e using Sym2.inductionOn with
  | _ x y =>
    exact Finset.disjoint_left.mp hST (hs' (by simp : x∈s(x,y).toFinset)) (ht' (by simp : x∈s(x,y).toFinset))

 theorem internalEdges_total_le {I V : Type*} [Fintype I] [Fintype V]
    (G : SimpleGraph V) (B : I → Finset V)
    (hB : ∀ i j, i≠j → Disjoint (B i) (B j)) :
    ∑ i, (internalEdges G (B i)).card ≤ G.edgeFinset.card := by
  classical
  have hd : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => internalEdges G (B i)) := by
    intro i hi j hj hij
    exact internalEdges_disjoint G (hB i j hij)
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro e he
  obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_filter.mp he).1

 theorem unit_short_walk {V : Type*} {G : SimpleGraph V}
    (w : Sym2 V → ℝ) (hw : ∀ e∈G.edgeSet, w e=1)
    (S : Finset V) (t : ℕ) {x y : V}
    (p : G.Walk x y) (hp : ∀ z∈p.support, z∈S) (hlen : p.length≤t) :
    ∃ q : G.Walk x y, (∀ z∈q.support, z∈S) ∧
      walkWeight w q ≤ (min (S.card-1) t : ℕ) := by
  classical
  let q := p.toPath
  have hsub : q.val.support.toFinset ⊆ S := by
    intro z hz
    exact hp z (p.support_toPath_subset_support (List.mem_toFinset.mp hz))
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup q.property.support_nodup,Walk.length_support] at hc
  have hqt : q.val.length≤t := le_trans p.length_bypass_le_length hlen
  have hqmin : q.val.length≤min (S.card-1) t := le_min (by omega) hqt
  have heq := walkWeight_eq_length_mul q.val w 1
    (fun e he => hw e (q.val.edges_subset_edgeSet he))
  refine ⟨q.val,fun z hz => hp z (p.support_toPath_subset_support hz),?_⟩
  rw [heq,mul_one]
  exact_mod_cast hqmin

end MinorFreeSpanners
