import MinorFreeSpanners.GeneralStarForest

/-! Add an actual disjoint star while retaining every original branch.
The canonical family has one more center and its covered set is an exact union. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

def adjoinStarLeaves (L : V → Finset V) (c : V) (S : Finset V) : V → Finset V :=
  Function.update L c (S.erase c)

theorem adjoinStar_branch_center (L : V → Finset V) (c : V) (S : Finset V)
    (hc : c ∈ S) : insert c (adjoinStarLeaves L c S c)=S := by
  simp [adjoinStarLeaves,Finset.insert_erase hc]

theorem adjoinStar_branch_old (L : V → Finset V) (c : V) (S : Finset V)
    {b : V} (hbc : b ≠ c) :
    insert b (adjoinStarLeaves L c S b)=insert b (L b) := by
  simp [adjoinStarLeaves,hbc]

theorem star_center_not_covered {C S : Finset V} {L : V → Finset V} {c : V}
    (hc : c ∈ S) (hdis : Disjoint S (C.biUnion fun b => insert b (L b))) : c ∉ C := by
  intro hC
  exact Finset.disjoint_left.mp hdis hc (Finset.mem_biUnion.mpr ⟨c,hC,by simp⟩)

theorem adjoinStar_covered (C S : Finset V) (L : V → Finset V) (c : V)
    (hc : c ∈ S) (hC : c ∉ C) :
    (insert c C).biUnion (fun b => insert b (adjoinStarLeaves L c S b))=
      S ∪ C.biUnion (fun b => insert b (L b)) := by
  rw [Finset.biUnion_insert,adjoinStar_branch_center L c S hc]
  congr 1
  apply Finset.biUnion_congr rfl
  intro b hb
  exact adjoinStar_branch_old L c S (fun he => hC (he ▸ hb))

theorem IsGeneralStarForest.adjoin {G : SimpleGraph V} {k : ℕ}
    {C S : Finset V} {L : V → Finset V} {c : V}
    (h : IsGeneralStarForest G k C L) (hc : c ∈ S) (hs : S.card=k)
    (hadj : ∀ x ∈ S, x ≠ c → G.Adj c x)
    (hdis : Disjoint S (C.biUnion fun b => insert b (L b))) :
    IsGeneralStarForest G k (insert c C) (adjoinStarLeaves L c S) := by
  have hC := star_center_not_covered hc hdis
  have hbc : ∀ b ∈ C, b ≠ c := fun b hb he => hC (he ▸ hb)
  refine ⟨?_,?_,?_⟩
  · intro b hb x hx
    rcases Finset.mem_insert.mp hb with he | hb
    · subst b
      have hx' : x ≠ c ∧ x ∈ S := by simpa [adjoinStarLeaves] using hx
      exact hadj x hx'.2 hx'.1
    · apply h.1 b hb x
      simpa [adjoinStarLeaves,hbc b hb] using hx
  · intro b hb
    rcases Finset.mem_insert.mp hb with he | hb
    · subst b
      rw [adjoinStar_branch_center L c S hc];exact hs
    · rw [adjoinStar_branch_old L c S (hbc b hb)];exact h.2.1 b hb
  · intro b hb a ha hba
    rcases Finset.mem_insert.mp hb with he | hb
    · subst b
      have hac : a ≠ c := Ne.symm hba
      have haC := (Finset.mem_insert.mp ha).resolve_left hac
      rw [adjoinStar_branch_center L c S hc,adjoinStar_branch_old L c S hac]
      apply Finset.disjoint_left.mpr
      intro x hx hxa
      exact Finset.disjoint_left.mp hdis hx (Finset.mem_biUnion.mpr ⟨a,haC,hxa⟩)
    · rcases Finset.mem_insert.mp ha with he | ha
      · subst a
        rw [adjoinStar_branch_old L c S (hbc b hb),adjoinStar_branch_center L c S hc]
        apply Finset.disjoint_left.mpr
        intro x hx hxc
        exact Finset.disjoint_left.mp hdis hxc (Finset.mem_biUnion.mpr ⟨b,hb,hx⟩)
      · rw [adjoinStar_branch_old L c S (hbc b hb),adjoinStar_branch_old L c S (hbc a ha)]
        exact h.2.2 b hb a ha hba

end MinorFreeSpanners
