import MinorFreeSpanners.RadiusTwoClusterWalks

/-! Actual connected finite sets of every smaller size. These are used as
internally selected cores for initial unit-tree clustering. -/
namespace MinorFreeSpanners
open SimpleGraph Finset

def ConnectedWithin {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x∈S, ∀ y∈S, ∃ p : G.Walk x y, ∀ z∈p.support, z∈S

namespace ConnectedWithin
variable {V : Type*} {G : SimpleGraph V} {S T : Finset V}

 theorem short_walk (hS : ConnectedWithin G S) {x y : V} (hx : x∈S) (hy : y∈S) :
    ∃ p : G.Walk x y, (∀ z∈p.support, z∈S) ∧ p.length < S.card := by
  classical
  obtain ⟨p,hp⟩ := hS x hx y hy
  let q := p.toPath
  have hsub : q.val.support.toFinset ⊆ S := by
    intro z hz
    exact hp z (p.support_toPath_subset_support (List.mem_toFinset.mp hz))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup q.property.support_nodup,Walk.length_support] at hcard
  exact ⟨q.val,fun z hz => hp z (p.support_toPath_subset_support hz),by omega⟩

 theorem boundary (hT : ConnectedWithin G T) (hST : S ⊆ T)
    (hne : S.Nonempty) (hlt : S.card < T.card) :
    ∃ x∈S, ∃ y∈T, y∉S ∧ G.Adj x y := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hnot : ¬T ⊆ S := by intro h;have hc:=Finset.card_le_card h;omega
  obtain ⟨y,hy,hys⟩ := Finset.not_subset.mp hnot
  obtain ⟨p,hp⟩ := hT x (hST hx) y hy
  obtain ⟨d,hd,hds,hdt⟩ := p.exists_boundary_dart (S:Set V) hx hys
  have hysupp : d.snd∈p.support :=
    (Walk.mem_darts_iff_fst_snd_infix_support.mp hd).subset (by simp)
  exact ⟨d.fst,hds,d.snd,hp _ hysupp,hdt,d.adj⟩

 theorem insert_adj [DecidableEq V] (hS : ConnectedWithin G S)
    {x y : V} (hx : x∈S) (hxy : G.Adj x y) : ConnectedWithin G (insert y S) := by
  have root (z : V) (hz : z∈insert y S) :
      ∃ p : G.Walk z x, ∀ v∈p.support, v∈insert y S := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · refine ⟨.cons hxy.symm .nil,?_⟩
      simp [hx]
    · obtain ⟨p,hp⟩ := hS z hz x hx
      exact ⟨p,fun v hv => Finset.mem_insert_of_mem (hp v hv)⟩
  intro a ha b hb
  obtain ⟨p,hp⟩ := root a ha
  obtain ⟨q,hq⟩ := root b hb
  refine ⟨p.append q.reverse,?_⟩
  intro z hz
  rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact hp z hz
  · exact hq z (by simpa using hz)

 theorem exists_subset_card (hT : ConnectedWithin G T) (k : ℕ) (hk : k≤T.card) :
    ∃ S : Finset V, S ⊆ T ∧ S.card=k ∧ ConnectedWithin G S := by
  classical
  induction k with
  | zero => exact ⟨∅,by simp,by simp,by simp [ConnectedWithin]⟩
  | succ k ih =>
    by_cases hz : k=0
    · subst k
      obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<T.card by omega)
      refine ⟨{v},by simpa using hv,by simp,?_⟩
      intro x hx y hy
      simp only [Finset.mem_singleton] at hx hy
      subst x;subst y
      exact ⟨.nil,by simp⟩
    · obtain ⟨S,hST,hcard,hS⟩ := ih (by omega)
      obtain ⟨x,hx,y,hy,hys,hxy⟩ := hT.boundary hST
        (Finset.card_pos.mp (by omega)) (by omega)
      exact ⟨insert y S,Finset.insert_subset hy hST,by simp [hys,hcard],hS.insert_adj hx hxy⟩

end ConnectedWithin
end MinorFreeSpanners
