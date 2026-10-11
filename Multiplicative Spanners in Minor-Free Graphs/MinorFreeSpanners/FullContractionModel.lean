import MinorFreeSpanners.EdgeContraction

/-! Full covering models retain every original vertex and every crossing
adjacency. These properties distinguish an actual contraction quotient from
an arbitrary minor whose target edges might have been deleted. -/
namespace MinorFreeSpanners
open SimpleGraph
namespace MinorModel
variable {I J V : Type*} {F : SimpleGraph I} {Q : SimpleGraph J} {G : SimpleGraph V}

/-- Every original vertex belongs to a branch. -/
def Covers (M : MinorModel F G) : Prop := ∀ x, ∃ i, x ∈ M.branch i

/-- Every actual crossing host edge is retained in the simple quotient. -/
def IsFull (M : MinorModel F G) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ M.branch i, ∀ y ∈ M.branch j, G.Adj x y → F.Adj i j

theorem Covers.comp (M : MinorModel Q F) (N : MinorModel F G)
    (hM : M.Covers) (hN : N.Covers) : (M.comp N).Covers := by
  intro x
  obtain ⟨i,hi⟩ := hN x
  obtain ⟨j,hj⟩ := hM i
  exact ⟨j,i,hj,hi⟩

theorem IsFull.comp (M : MinorModel Q F) (N : MinorModel F G)
    (hM : M.IsFull) (hN : N.IsFull) : (M.comp N).IsFull := by
  rintro i j hij x ⟨a,hai,hxa⟩ y ⟨b,hbj,hyb⟩ hxy
  have hab : a ≠ b := by
    intro he
    subst b
    exact Set.disjoint_left.mp (M.disjoint i j hij) hai hbj
  exact hM i j hij a hai b hbj (hN a b hab x hxa y hyb hxy)

/-- The unchanged host itself, with literal singleton branches. -/
def identity (G : SimpleGraph V) : MinorModel G G :=
  MinorModel.ofEmbedding G G (Function.Embedding.refl V) (fun _ _ h => h)

theorem identity_covers (G : SimpleGraph V) : (identity G).Covers :=
  fun x => ⟨x,rfl⟩

theorem identity_full (G : SimpleGraph V) : (identity G).IsFull := by
  intro i j _ x hx y hy hxy
  have hx' : x=i := hx
  have hy' : y=j := hy
  simpa [hx',hy'] using hxy

theorem identity_bounded [Fintype V] (G : SimpleGraph V) :
    (identity G).IsBounded 1 := by
  classical
  intro i
  simp [identity,MinorModel.ofEmbedding]

end MinorModel

/-- Single-edge contraction retains every old vertex in one of its actual
branches, including the absorbed endpoint. -/
theorem contractEdgeModel_covers {V : Type*} (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) : (contractEdgeModel G u v huv).Covers := by
  intro x
  by_cases hx : x=v
  · exact ⟨⟨u,huv.ne⟩,Or.inr ⟨rfl,hx⟩⟩
  · exact ⟨⟨x,hx⟩,Or.inl rfl⟩

/-- No crossing adjacency is lost except by the intended vertex merge;
loops and parallel copies are represented by the actual simple contraction. -/
theorem contractEdgeModel_full {V : Type*} (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) : (contractEdgeModel G u v huv).IsFull := by
  rintro i j hij x (hx | ⟨hi,hx⟩) y (hy | ⟨hj,hy⟩) hxy
  · subst x; subst y
    exact ⟨hij,Or.inl hxy⟩
  · subst x; subst y
    exact ⟨hij,Or.inr (Or.inr ⟨hj,hxy⟩)⟩
  · subst x; subst y
    exact ⟨hij,Or.inr (Or.inl ⟨hi,hxy⟩)⟩
  · exact (hxy.ne (hx.trans hy.symm)).elim

end MinorFreeSpanners
