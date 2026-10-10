import MinorFreeSpanners.FullStarContraction
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Literal directed crossing-leaf sets between two selected stars.
A source-style bad pair has exactly one crossing in each direction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- Leaves of b adjacent to the other center c. -/
noncomputable def starCrossLeaves (G : SimpleGraph V) (L : V → Finset V)
    (b c : V) : Finset V := (L b).filter fun x => G.Adj x c

/-- Exactly two oppositely oriented crossing edges between distinct stars. -/
def IsBadStarPair (G : SimpleGraph V) (L : V → Finset V) (b c : V) : Prop :=
  b ≠ c ∧ (starCrossLeaves G L b c).card = 1 ∧ (starCrossLeaves G L c b).card = 1

theorem isBadStarPair_symm (G : SimpleGraph V) (L : V → Finset V) {b c : V}
    (h : IsBadStarPair G L b c) : IsBadStarPair G L c b := ⟨h.1.symm,h.2.2,h.2.1⟩

/-- The two actual forest leaves witnessing a bad pair are uniquely fixed
by the corresponding actual crossing neighborhoods. -/
theorem badStarPair_unique_leaves (G : SimpleGraph V) (L : V → Finset V)
    {b c : V} (h : IsBadStarPair G L b c) :
    ∃ u ∈ L b, ∃ v ∈ L c, G.Adj u c ∧ G.Adj v b ∧
      (∀ x ∈ L b, G.Adj x c ↔ x=u) ∧
      (∀ y ∈ L c, G.Adj y b ↔ y=v) := by
  classical
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp h.2.1
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h.2.2
  have hu' : u ∈ L b ∧ G.Adj u c := by
    have hm : u ∈ starCrossLeaves G L b c := by rw [hu]; simp
    exact Finset.mem_filter.mp hm
  have hv' : v ∈ L c ∧ G.Adj v b := by
    have hm : v ∈ starCrossLeaves G L c b := by rw [hv]; simp
    exact Finset.mem_filter.mp hm
  refine ⟨u,hu'.1,v,hv'.1,hu'.2,hv'.2,?_,?_⟩
  · intro x hx
    have he : (x ∈ L b ∧ G.Adj x c) ↔ x=u := by
      have h0 : x ∈ starCrossLeaves G L b c ↔ x=u := by rw [hu]; simp
      simpa only [starCrossLeaves,Finset.mem_filter] using h0
    exact ⟨fun h => he.mp ⟨hx,h⟩,by rintro rfl; exact hu'.2⟩
  · intro y hy
    have he : (y ∈ L c ∧ G.Adj y b) ↔ y=v := by
      have h0 : y ∈ starCrossLeaves G L c b ↔ y=v := by rw [hv]; simp
      simpa only [starCrossLeaves,Finset.mem_filter] using h0
    exact ⟨fun h => he.mp ⟨hy,h⟩,by rintro rfl; exact hv'.2⟩

/-- All literal host edges between the two center-plus-leaf sets. -/
noncomputable def starBetweenEdges (G : SimpleGraph V) (L : V → Finset V)
    (b c : V) : Finset (Sym2 V) :=
  (((insert b (L b)).product (insert c (L c))).filter
    fun p => G.Adj p.1 p.2).image fun p => s(p.1,p.2)

/-- In the bipartite host every crossing edge has exactly one of the two
center-to-opposite-leaf orientations. -/
theorem starBetweenEdges_eq (G : SimpleGraph V) (A B : Finset V)
    (L : V → Finset V) (b c : V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (hb : b ∈ B) (hc : c ∈ B)
    (hLb : L b ⊆ A) (hLc : L c ⊆ A) :
    starBetweenEdges G L b c =
      (starCrossLeaves G L b c).image (fun x => s(x,c)) ∪
      (starCrossLeaves G L c b).image (fun y => s(b,y)) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxy,hadj⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    rcases Finset.mem_insert.mp hx with rfl|hx <;>
      rcases Finset.mem_insert.mp hy with rfl|hy
    · exact (Set.disjoint_left.mp hG.disjoint
        (hG.symm.mem_of_mem_adj hb hadj) hc).elim
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨y,Finset.mem_filter.mpr ⟨hy,hadj.symm⟩,rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨x,Finset.mem_filter.mpr ⟨hx,hadj⟩,rfl⟩)
    · exact (Set.disjoint_left.mp hG.disjoint (hLc hy)
        (hG.mem_of_mem_adj (hLb hx) hadj)).elim
  · intro he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨(x,c),Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_insert_of_mem hx,Finset.mem_insert_self _ _⟩,he⟩,rfl⟩
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hy,he⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨(b,y),Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem hy⟩,he.symm⟩,rfl⟩

/-- Distinct bipartite stars have exactly p+q crossing host edges, with
p and q the two directed crossing-neighborhood cardinalities. -/
theorem starBetweenEdges_card (G : SimpleGraph V) (A B : Finset V)
    (L : V → Finset V) (b c : V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (hb : b ∈ B) (hc : c ∈ B) (hbc : b ≠ c)
    (hLb : L b ⊆ A) (hLc : L c ⊆ A) :
    (starBetweenEdges G L b c).card =
      (starCrossLeaves G L b c).card + (starCrossLeaves G L c b).card := by
  classical
  rw [starBetweenEdges_eq G A B L b c hG hb hc hLb hLc]
  have hd : Disjoint ((starCrossLeaves G L b c).image (fun x => s(x,c)))
      ((starCrossLeaves G L c b).image (fun y => s(b,y))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hf
    rcases Sym2.eq_iff.mp heq with ⟨hbx,_⟩|⟨hbc',_⟩
    · exact Set.disjoint_left.mp hG.disjoint
        (hbx.symm ▸ hLb (Finset.mem_filter.mp hx).1) hb
    · exact hbc hbc'
  rw [Finset.card_union_of_disjoint hd]
  have hi (z : V) : Function.Injective (fun x : V => s(z,x)) := by
    intro x y he
    rcases Sym2.eq_iff.mp he with ⟨_,he⟩|⟨h1,h2⟩
    · exact he
    · exact h2.trans h1
  have hi' (z : V) : Function.Injective (fun x : V => s(x,z)) := by
    intro x y he
    exact hi z (Sym2.eq_swap.trans (he.trans Sym2.eq_swap))
  rw [Finset.card_image_of_injective _ (hi' c),Finset.card_image_of_injective _ (hi b)]

end MinorFreeSpanners
