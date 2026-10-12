import MinorFreeSpanners.WeightedPathArms

/-! Joining two genuinely rooted branch unions through one original host
edge uses that edge at most once. The resulting paths stay in the union. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners

 theorem walkWeight_reverse {V : Type*} {G : SimpleGraph V} (w : Sym2 V → ℝ)
    {a b : V} (p : G.Walk a b) : walkWeight w p.reverse=walkWeight w p := by
  simp [walkWeight]

 theorem rooted_sets_bridge {V : Type*} {G : SimpleGraph V}
    (w : Sym2 V → ℝ) (S T : Set V) {x y : V} (hxy : G.Adj x y)
    (hx : x∈S) (R M : ℝ) (hM : 0≤M) (he : w s(x,y)≤M)
    (hS : ∀ a∈S,∃ p : G.Walk a x,(∀ z∈p.support,z∈S) ∧ walkWeight w p≤R)
    (hT : ∀ a∈T,∃ p : G.Walk a y,(∀ z∈p.support,z∈T) ∧ walkWeight w p≤R) :
    ∀ a∈S∪T,∀ b∈S∪T,∃ p : G.Walk a b,
      (∀ z∈p.support,z∈S∪T) ∧ walkWeight w p≤2*R+M := by
  have same {U : Set V} {r : V} (hU : U⊆S∪T)
      (hr : ∀ a∈U,∃ p : G.Walk a r,(∀ z∈p.support,z∈U) ∧ walkWeight w p≤R)
      {a b : V} (ha : a∈U) (hb : b∈U) :
      ∃ p : G.Walk a b,(∀ z∈p.support,z∈S∪T) ∧ walkWeight w p≤2*R+M := by
    obtain ⟨p,hp,hpw⟩ := hr a ha
    obtain ⟨q,hq,hqw⟩ := hr b hb
    refine ⟨p.append q.reverse,?_,?_⟩
    · intro z hz
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz|hz
      · exact hU (hp z hz)
      · exact hU (hq z (by simpa using hz))
    · rw [walkWeight_append,walkWeight_reverse]
      linarith
  have cross {a b : V} (ha : a∈S) (hb : b∈T) :
      ∃ p : G.Walk a b,(∀ z∈p.support,z∈S∪T) ∧ walkWeight w p≤2*R+M := by
    obtain ⟨p,hp,hpw⟩ := hS a ha
    obtain ⟨q,hq,hqw⟩ := hT b hb
    refine ⟨p.append (.cons hxy q.reverse),?_,?_⟩
    · intro z hz
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz|hz
      · exact Or.inl (hp z hz)
      · simp only [Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl|hz
        · exact Or.inl hx
        · exact Or.inr (hq z (by simpa using hz))
    · rw [walkWeight_append,walkWeight_cons,walkWeight_reverse]
      linarith
  intro a ha b hb
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · exact same Set.subset_union_left hS ha hb
  · exact cross ha hb
  · obtain ⟨p,hp,hw⟩ := cross hb ha
    exact ⟨p.reverse,fun z hz => hp z (by simpa using hz),by simpa only [walkWeight_reverse] using hw⟩
  · exact same Set.subset_union_right hT ha hb

end MinorFreeSpanners
