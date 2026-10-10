import LinearDistancePreservers.WeightedLexicographic

namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph WeightedNativeForcing
open scoped NNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

 theorem fullWalk_isPath [DecidableEq (Vertex A B C U)] (b : B) (j : J) :
    (fullWalk D b j).IsPath := by
  apply Walk.bypass_eq_self_iff_isPath.mp
  apply (Walk.length_le_bypass_length_iff (fullWalk D b j)).mp
  exact fullWalk_shortest D b j _

 theorem real_product_positive (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (wi : U → U → ℝ≥0) (δ : ℝ≥0) (hδ : 0 < δ)
    (hl : ∀ b j, 0 < wl (D.left b j) b)
    (hr : ∀ b j, 0 < wr b (D.right b j))
    (hi : ∀ u v, (innerGraph D).Adj u v → 0 < wi u v)
    (s t : Vertex A B C U) (h : (graph D).Adj s t) :
    0 < realPrimary wl wr s t + δ * realSecondary wi s t := by
  rcases h with ⟨e,h | h⟩ <;>
    have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;>
    dsimp at hs ht
  · rw [← hs,← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
    · simpa [arc,realPrimary,outerWeight,projectVertex,realSecondary] using hl b j
    · simpa [arc,realPrimary,outerWeight,projectVertex,realSecondary] using
        mul_pos hδ (hi _ _ ⟨i,j,Or.inl ⟨rfl,rfl⟩⟩)
    · simpa [arc,realPrimary,outerWeight,projectVertex,realSecondary] using hr b j
  · rw [← ht,← hs]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
    · simpa [arc,realPrimary,outerWeight,projectVertex,realSecondary] using hl b j
    · simpa [arc,realPrimary,outerWeight,projectVertex,realSecondary] using
        mul_pos hδ (hi _ _ ⟨i,j,Or.inr ⟨rfl,rfl⟩⟩)
    · simpa [arc,realPrimary,outerWeight,projectVertex,realSecondary] using hr b j

/-- Generic positive-real weighted obstacle-product metric join. Input
hypotheses concern actual native walks in the outer and inner graphs. One
positive scale, chosen before all endpoints and competitors, works uniformly.
There is no integral-weight, gap-size, baseline, or product-optimality premise. -/
theorem exists_real_weighted_product [Fintype A] [Fintype B] [Fintype C] [Fintype U]
    (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) (wi : U → U → ℝ≥0)
    (hl : ∀ b j, 0 < wl (D.left b j) b)
    (hr : ∀ b j, 0 < wr b (D.right b j))
    (hi : ∀ u v, (innerGraph D).Adj u v → 0 < wi u v)
    (hout : RealOuterOptimal D wl wr) (hin : RealInnerOptimal D wi) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ ε →
      ∀ b j (q : (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j)))),
        let weight := fun s t => realPrimary wl wr s t + δ * realSecondary wi s t
        realCost weight (fullWalk D b j) ≤ realCost weight q ∧
        (realCost weight q = realCost weight (fullWalk D b j) → q = fullWalk D b j) := by
  classical
  obtain ⟨ε,hε,hscale⟩ := exists_path_perturbation (graph D) (realPrimary wl wr) (realSecondary wi)
  refine ⟨ε,hε,?_⟩
  intro δ hδ hδε b j q
  dsimp only
  let weight := fun s t => realPrimary wl wr s t + δ * realSecondary wi s t
  let p : (graph D).Path (.inl (D.left b j)) (.inr (.inr (D.right b j))) :=
    ⟨fullWalk D b j,fullWalk_isPath D b j⟩
  have hstrict : ∀ r : (graph D).Path (.inl (D.left b j)) (.inr (.inr (D.right b j))),
      r.val ≠ fullWalk D b j → realCost weight (fullWalk D b j) < realCost weight r.val := by
    intro r hne
    exact hscale δ hδ hδε _ _ p r (real_lexicographic D wl wr wi hout hin b j r.val hne)
  apply path_optimal_to_walk weight (real_product_positive D wl wr wi δ hδ hl hr hi) (fullWalk D b j)
  · intro r
    by_cases he : r.val = fullWalk D b j
    · rw [he]
    · exact (hstrict r he).le
  · intro r he
    by_contra hne
    exact (hstrict r hne).ne he.symm

end LinearDistancePreservers.ObstacleProduct

namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph WeightedNativeForcing Finset
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

 theorem outerWeight_symmetric (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (u v : OuterVertex A B C) : outerWeight wl wr u v = outerWeight wl wr v u := by
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c') <;> rfl

 theorem product_weight_symmetric (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (wi : U → U → ℝ≥0) (hs : ∀ u v, wi u v = wi v u) (δ : ℝ≥0)
    (u v : Vertex A B C U) :
    realPrimary wl wr u v + δ * realSecondary wi u v =
      realPrimary wl wr v u + δ * realSecondary wi v u := by
  unfold realPrimary
  rw [outerWeight_symmetric wl wr (projectVertex u) (projectVertex v)]
  congr 1
  congr 1
  rcases u with a | (⟨b,s⟩ | c) <;> rcases v with a' | (⟨b',t⟩ | c') <;>
    simp [realSecondary,hs]

/-- The same generic scale forces every actual edge of the obstacle product
under preservation of the designated native weighted endpoint distances. -/
theorem exists_real_weighted_forcing [Fintype A] [Fintype B] [Fintype C] [Fintype U] [Fintype J]
    (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) (wi : U → U → ℝ≥0)
    (hl : ∀ b j, 0 < wl (D.left b j) b)
    (hr : ∀ b j, 0 < wr b (D.right b j))
    (hi : ∀ u v, (innerGraph D).Adj u v → 0 < wi u v)
    (hout : RealOuterOptimal D wl wr) (hin : RealInnerOptimal D wi) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ ε →
      let weight := fun s t => realPrimary wl wr s t + δ * realSecondary wi s t
      ∀ H : SimpleGraph (Vertex A B C U), H ≤ graph D →
        (∀ b j, WeightedDigraph.distance H.Adj (fun u v => (weight u v : ℝ≥0∞))
          (.inl (D.left b j)) (.inr (.inr (D.right b j))) =
        WeightedDigraph.distance (graph D).Adj (fun u v => (weight u v : ℝ≥0∞))
          (.inl (D.left b j)) (.inr (.inr (D.right b j)))) →
        H = graph D ∧ H.edgeFinset.card = Fintype.card B * Fintype.card J * (k+2) := by
  classical
  obtain ⟨ε,hε,hmetric⟩ := exists_real_weighted_product D wl wr wi hl hr hi hout hin
  refine ⟨ε,hε,?_⟩
  intro δ hδ hδε
  dsimp only
  intro H hsub hpres
  let weight := fun s t => realPrimary wl wr s t + δ * realSecondary wi s t
  have hcover : ∀ e ∈ (graph D).edgeSet,
      ∃ p : B × J, e ∈ (fullWalk D p.1 p.2).edges := by
    intro e he
    have hf : e ∈ (graph D).edgeFinset := by simpa using he
    rw [graph_edgeFinset] at hf
    obtain ⟨i, _, rfl⟩ := mem_image.mp hf
    obtain ⟨b,j,hbj⟩ := indexed_edge_covered D i
    exact ⟨(b,j), hbj⟩
  have heq := WeightedNativeForcing.eq_of_covers weight
    (fun p : B × J => (.inl (D.left p.1 p.2) : Vertex A B C U))
    (fun p : B × J => (.inr (.inr (D.right p.1 p.2)) : Vertex A B C U))
    (fun p => fullWalk D p.1 p.2)
    (fun p q => (hmetric δ hδ hδε p.1 p.2 q).1)
    (fun p q => (hmetric δ hδ hδε p.1 p.2 q).2)
    hcover hsub (fun p => hpres p.1 p.2)
  exact ⟨heq,by rw [heq]; exact edge_count D⟩

end LinearDistancePreservers.ObstacleProduct
