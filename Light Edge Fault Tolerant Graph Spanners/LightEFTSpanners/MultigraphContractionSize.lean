import LightEFTSpanners.MultigraphCutTransport

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- The contracted outside vertex is genuine precisely when there is an
outside preimage; all retained core vertices always have their own preimages. -/
theorem collapseOutside_surjective (K : Set V) (hout : ∃ v,v∉K) :
    Function.Surjective (collapseOutside K) := by
  intro x
  cases x with
  | none =>
    obtain ⟨v,hv⟩ := hout
    exact ⟨v,by simp [collapseOutside,hv]⟩
  | some a => exact ⟨a.val,by simp [collapseOutside,a.property]⟩

/-- For a proper retained set in a full-vertex native graph, every vertex of
its contraction's ambient type is actual. This invariant makes subsequent
finite vertex-type cardinality calculations genuine graph-order calculations. -/
theorem native_collapse_vertexSet (G : Graph V E) (hall : G.vertexSet=Set.univ)
    (K : Set V) (hout : ∃ v,v∉K) :
    (G.map (collapseOutside K)).vertexSet=Set.univ := by
  change collapseOutside K '' G.vertexSet=Set.univ
  rw [hall]
  exact Set.image_univ_of_surjective (collapseOutside_surjective K hout)

/-- The full-vertex premise above holds for every embedded simple graph. -/
theorem collapse_vertexSet (G : SimpleGraph V) (K : Set V) (hout : ∃ v,v∉K) :
    ((Graph.ofSimpleGraph G).map (collapseOutside K)).vertexSet=Set.univ :=
  native_collapse_vertexSet (Graph.ofSimpleGraph G) rfl K hout

/-- Contracting a core of at least two vertices to one strictly lowers the
finite vertex-type count. With the full-vertex invariant above this is the
actual graph-order decrease used in the packing induction. This lemma alone
does not assert that an arbitrary ambient type consists of actual vertices. -/
theorem contract_core_card_lt [Fintype V] (K : Finset V) (hK : 2≤K.card) :
    Fintype.card (Option {v : V // v∉K})<Fintype.card V := by
  classical
  have hcard := Finset.card_compl_add_card K
  have hc : Fintype.card {v : V // v∉K}=(Kᶜ).card := by
    simp
    omega
  rw [Fintype.card_option,hc]
  omega
end LightEFTSpanners.MultigraphCuts
