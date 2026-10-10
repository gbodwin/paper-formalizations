import MinorFreeSpanners.MinorRestriction

namespace MinorFreeSpanners
open SimpleGraph
variable {I V W : Type*} {F : SimpleGraph I} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A vertex map that collapses edges or maps them to edges sends actual
walks to actual walks after deleting the collapsed steps, with support control. -/
theorem map_walk_with_collapses (f : V → W)
    (hf : ∀ {x y}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    {u v : V} (p : G.Walk u v) (S : Set V) (hS : ∀ x ∈ p.support, x ∈ S) :
    ∃ q : H.Walk (f u) (f v), ∀ y ∈ q.support, y ∈ f '' S := by
  induction p with
  | @nil u =>
    refine ⟨.nil,?_⟩
    intro y hy
    have hy' : y = f u := by simpa using hy
    subst y
    exact ⟨_,hS _ (by simp),rfl⟩
  | @cons u v z huv p ih =>
    obtain ⟨q,hq⟩ := ih (fun x hx => hS x (by simp [hx]))
    rcases hf huv with he | he
    · rw [he]
      exact ⟨q,hq⟩
    · refine ⟨.cons he q,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨u,hS u (by simp),rfl⟩
      · exact hq y hy

/-- A genuine minor-model image under edge collapses, provided distinct
branches have disjoint images. The support and crossing edges are constructed. -/
noncomputable def MinorModel.mapWeak (M : MinorModel F G) (f : V → W)
    (hf : ∀ {x y}, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ M.branch i, ∀ y ∈ M.branch j, f x ≠ f y) :
    MinorModel F H where
  branch := fun i => f '' M.branch i
  nonempty := fun i => (M.nonempty i).image f
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    exact hsep i j hij x hx y hy he.symm
  connected := by
    rintro i _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    obtain ⟨p,hp⟩ := M.connected i x hx y hy
    exact map_walk_with_collapses f hf p (M.branch i) hp
  adjacent := by
    intro i j hij
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent i j hij
    exact ⟨f x,⟨x,hx,rfl⟩,f y,⟨y,hy,rfl⟩,
      (hf hxy).resolve_left (hsep i j hij.ne x hx y hy)⟩

end MinorFreeSpanners
