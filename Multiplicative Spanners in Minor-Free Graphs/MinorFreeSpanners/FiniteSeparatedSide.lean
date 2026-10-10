import MinorFreeSpanners.RobustCommonNeighbors

/-! An actual finite side of a disconnected graph, and its pullback through
vertex deletion. No separator oracle is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A graph which is not preconnected has a nonempty edge-closed side
containing at most half its vertices. -/
theorem exists_closed_small_side (G : SimpleGraph V) (hG : ¬G.Preconnected) :
    ∃ A : Finset V, A.Nonempty ∧ 2*A.card ≤ Fintype.card V ∧
      ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A := by
  classical
  unfold SimpleGraph.Preconnected at hG
  push Not at hG
  obtain ⟨u,v,huv⟩ := hG
  let R := Finset.univ.filter fun x => G.Reachable u x
  have hR : ∀ x, x ∈ R ↔ G.Reachable u x := by intro x; simp [R]
  have hu : u ∈ R := (hR u).mpr (SimpleGraph.Reachable.refl u)
  have hv : v ∉ R := fun hv => huv ((hR v).mp hv)
  have hclosed : ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R := by
    intro x hx y hxy
    exact (hR y).mpr (((hR x).mp hx).trans hxy.reachable)
  by_cases hsmall : 2*R.card ≤ Fintype.card V
  · exact ⟨R,⟨u,hu⟩,hsmall,hclosed⟩
  · refine ⟨Rᶜ,⟨v,by simpa using hv⟩,?_,?_⟩
    · rw [Finset.card_compl]
      have hc := Finset.card_le_univ R
      omega
    · intro x hx y hxy
      simp only [Finset.mem_compl] at hx ⊢
      intro hy
      exact hx (hclosed y hy x hxy.symm)

/-- Failure of deletion robustness supplies an actual nonempty small side
whose only possible external neighbors lie in the deleted separator. -/
theorem exists_separator_side (G : SimpleGraph V) (q : ℕ)
    (hG : ¬DeletionConnected G q) :
    ∃ S A : Finset V, S.card < q ∧ A.Nonempty ∧ Disjoint A S ∧
      2*A.card ≤ Fintype.card V ∧
      ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y ∈ S := by
  classical
  unfold DeletionConnected at hG
  push Not at hG
  obtain ⟨S,hS,hpre⟩ := hG
  let W := {x : V // x ∉ S}
  let H := G.comap (Subtype.val : W → V)
  change ¬H.Preconnected at hpre
  obtain ⟨A,hA,hcard,hclosed⟩ := exists_closed_small_side H hpre
  let B := A.map (Function.Embedding.subtype fun x : V => x ∉ S)
  have hBcard : B.card = A.card := Finset.card_map _
  refine ⟨S,B,hS,?_,?_,?_,?_⟩
  · obtain ⟨x,hx⟩ := hA
    exact ⟨x.val,Finset.mem_map.mpr ⟨x,hx,rfl⟩⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxs
    obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
    exact y.property hxs
  · have hw := Fintype.card_le_of_injective (Subtype.val : W → V) Subtype.val_injective
    rw [hBcard]
    exact hcard.trans hw
  · intro x hx y hxy
    obtain ⟨xx,hxx,rfl⟩ := Finset.mem_map.mp hx
    by_cases hy : y ∈ S
    · exact Or.inr hy
    · apply Or.inl
      exact Finset.mem_map.mpr ⟨⟨y,hy⟩,hclosed xx hxx ⟨y,hy⟩ hxy,rfl⟩

end MinorFreeSpanners
