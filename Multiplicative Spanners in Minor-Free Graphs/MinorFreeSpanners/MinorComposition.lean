import MinorFreeSpanners.MinorEdgeCount

/-! Transitivity of the genuine branch-set minor model. All connecting
walks are constructed, rather than assuming a contraction oracle. -/
namespace MinorFreeSpanners
open SimpleGraph
namespace MinorModel
variable {I V W : Type*} {F : SimpleGraph I} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Lift a graph walk through a branch-set model, staying inside the union
of branch sets over the walk's support. -/
theorem lift_walk (N : MinorModel G H) {u v : V} (p : G.Walk u v)
    (S : Set W) (hS : ∀ x ∈ p.support, N.branch x ⊆ S)
    {a b : W} (ha : a ∈ N.branch u) (hb : b ∈ N.branch v) :
    ∃ q : H.Walk a b, ∀ z ∈ q.support, z ∈ S := by
  induction p generalizing a with
  | nil =>
    obtain ⟨q, hq⟩ := N.connected _ a ha b hb
    exact ⟨q, fun z hz => hS _ (by simp) (hq z hz)⟩
  | @cons u v z huv p ih =>
    obtain ⟨x, hxbranch, y, hy, hxy⟩ := N.adjacent u v huv
    obtain ⟨q₁, hq₁⟩ := N.connected u a ha x hxbranch
    obtain ⟨q₂, hq₂⟩ := ih (fun x hx => hS x (by simp [hx])) hy hb
    refine ⟨q₁.append (.cons hxy q₂), ?_⟩
    intro x hx
    rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
    · exact hS u (by simp) (hq₁ x hx)
    · simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hS u (by simp) hxbranch
      · exact hq₂ x hx

noncomputable def comp (M : MinorModel F G) (N : MinorModel G H) : MinorModel F H where
  branch := fun i => {w | ∃ v ∈ M.branch i, w ∈ N.branch v}
  nonempty := by
    intro i
    obtain ⟨v, hv⟩ := M.nonempty i
    obtain ⟨w, hw⟩ := N.nonempty v
    exact ⟨w,v,hv,hw⟩
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro w ⟨v,hvi,hwv⟩ ⟨u,huj,hwu⟩
    have he : v = u := N.branch_unique hwv hwu
    subst u
    exact Set.disjoint_left.mp (M.disjoint i j hij) hvi huj
  connected := by
    rintro i a ⟨u,hu,ha⟩ b ⟨v,hv,hb⟩
    obtain ⟨p,hp⟩ := M.connected i u hu v hv
    apply N.lift_walk p _ _ ha hb
    intro x hx w hw
    exact ⟨x,hp x hx,hw⟩
  adjacent := by
    intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := M.adjacent i j hij
    obtain ⟨x,hx,y,hy,hxy⟩ := N.adjacent u v huv
    exact ⟨x,⟨u,hu,hx⟩,y,⟨v,hv,hy⟩,hxy⟩
end MinorModel

theorem CliqueMinorFree.of_minor {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {h : ℕ} (hH : CliqueMinorFree H h) (M : MinorModel G H) : CliqueMinorFree G h := by
  rintro ⟨N⟩
  exact hH ⟨N.comp M⟩

end MinorFreeSpanners
