import MinorFreeSpanners.GreedyDominatingSet
import MinorFreeSpanners.ConnectFiniteSet
import MinorFreeSpanners.DenseGraphDiameter

/-! An actual small connected dominating set in a dense connected graph. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem exists_small_connected_dominating_set (G : SimpleGraph V) (δ : ℕ)
    (hδ : 0 < δ) (hconn : G.Connected)
    (hsize : Fintype.card V ≤ 4*δ) (hdeg : ∀ x, δ ≤ G.degree x) :
    ∃ C : Finset V, C.Nonempty ∧ C.card ≤ 48*(Nat.log 2 (Fintype.card V)+1) ∧
      (∀ x, ∃ v ∈ C, G.Adj v x) ∧
      ∀ x ∈ C, ∀ y ∈ C, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ C := by
  classical
  let := hconn.nonempty
  obtain ⟨B,hB,hdom⟩ := exists_small_dominating_set G δ hδ hsize hdeg
  have hBne : B.Nonempty := by
    obtain ⟨v,hv,_⟩ := hdom (Classical.arbitrary V)
    exact ⟨v,hv⟩
  have hwalk : ∀ u v, ∃ p : G.Walk u v, p.length ≤ 11 :=
    connected_exists_walk_length_le_eleven δ hδ hconn hdeg (by omega)
  obtain ⟨C,hBC,hC,hpaths⟩ := connect_finite_set G 11 hwalk B hBne
  refine ⟨C,hBne.mono hBC,?_,?_,hpaths⟩
  · nlinarith
  · intro x
    obtain ⟨v,hv,hvx⟩ := hdom x
    exact ⟨v,hBC hv,hvx⟩

end MinorFreeSpanners
