import MinorFreeSpanners.TwoBlockDiameterReserve

/-! Actual selected heavy edges attach many blocks to one old root carrier.
Every route uses at most two distinct blocks. The internally selected pair
reserve therefore bounds the diameter independently of the number attached. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem rooted_heavy_family_walks {V J : Type*} {G : SimpleGraph V}
    (w : Sym2 V → ℝ) (F : Finset J) (root : Set V) (block : J → Set V)
    (source target : J → V) (radius : J → ℝ) (R M z : ℝ)
    (hR : 0≤R) (hM : 0≤M) (hz : 0≤z)
    (hs : ∀ j∈F,source j∈root) (ht : ∀ j∈F,target j∈block j)
    (hedge : ∀ j∈F,G.Adj (source j) (target j))
    (hweight : ∀ j∈F,w s(source j,target j)≤M)
    (hroot : ∀ a∈root,∀ b∈root,∃ p : G.Walk a b,
      (∀ x∈p.support,x∈root) ∧ walkWeight w p≤R)
    (hblock : ∀ j∈F,∀ a∈block j,∀ b∈block j,∃ p : G.Walk a b,
      (∀ x∈p.support,x∈block j) ∧ walkWeight w p≤radius j)
    (hone : ∀ j∈F,radius j≤z)
    (htwo : ∀ i∈F,∀ j∈F,i≠j → radius i+radius j≤z) :
    let carrier := {x | x∈root ∨ ∃ j∈F,x∈block j}
    ∀ a∈carrier,∀ b∈carrier,∃ p : G.Walk a b,
      (∀ x∈p.support,x∈carrier) ∧ walkWeight w p≤R+2*M+z := by
  classical
  let carrier := {x | x∈root ∨ ∃ j∈F,x∈block j}
  change ∀ a∈carrier,∀ b∈carrier,∃ p : G.Walk a b,
    (∀ x∈p.support,x∈carrier) ∧ walkWeight w p≤R+2*M+z
  have hroot' {a b : V} (ha : a∈root) (hb : b∈root) :
      ∃ p : G.Walk a b,(∀ x∈p.support,x∈carrier) ∧ walkWeight w p≤R := by
    obtain ⟨p,hp,hw⟩ := hroot a ha b hb
    exact ⟨p,fun x hx => Or.inl (hp x hx),hw⟩
  have hto (j : J) (hj : j∈F) {a : V} (ha : a∈block j) :
      ∃ p : G.Walk a (source j),(∀ x∈p.support,x∈carrier) ∧
        walkWeight w p≤radius j+M := by
    obtain ⟨p,hp,hw⟩ := hblock j hj a ha (target j) (ht j hj)
    refine ⟨p.append (.cons (hedge j hj).symm .nil),?_,?_⟩
    · intro x hx
      rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
      · exact Or.inr ⟨j,hj,hp x hx⟩
      · simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl
        · exact Or.inr ⟨j,hj,ht j hj⟩
        · exact Or.inl (hs j hj)
    · rw [walkWeight_append,walkWeight_cons,walkWeight_nil,add_zero]
      have he := hweight j hj
      simpa only [Sym2.eq_swap] using (add_le_add hw he)
  have hcross {a b : V} (ha : a∈root) (j : J) (hj : j∈F) (hb : b∈block j) :
      ∃ p : G.Walk a b,(∀ x∈p.support,x∈carrier) ∧ walkWeight w p≤R+2*M+z := by
    obtain ⟨p,hp,hw⟩ := hroot' ha (hs j hj)
    obtain ⟨q,hq,hqw⟩ := hto j hj hb
    refine ⟨p.append q.reverse,?_,?_⟩
    · intro x hx
      rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
      · exact hp x hx
      · exact hq x (by simpa using hx)
    · rw [walkWeight_append,walkWeight_reverse]
      linarith [hone j hj]
  intro a ha b hb
  rcases ha with ha | ⟨i,hi,ha⟩ <;> rcases hb with hb | ⟨j,hj,hb⟩
  · obtain ⟨p,hp,hw⟩ := hroot' ha hb
    exact ⟨p,hp,by linarith⟩
  · exact hcross ha j hj hb
  · obtain ⟨p,hp,hw⟩ := hcross hb i hi ha
    exact ⟨p.reverse,fun x hx => hp x (by simpa using hx),by simpa only [walkWeight_reverse] using hw⟩
  · by_cases hij : i=j
    · subst j
      obtain ⟨p,hp,hw⟩ := hblock i hi a ha b hb
      exact ⟨p,fun x hx => Or.inr ⟨i,hi,hp x hx⟩,by linarith [hone i hi]⟩
    · obtain ⟨p,hp,hw⟩ := hto i hi ha
      obtain ⟨q,hq,hqw⟩ := hroot' (hs i hi) (hs j hj)
      obtain ⟨r,hr,hrw⟩ := hto j hj hb
      refine ⟨p.append (q.append r.reverse),?_,?_⟩
      · intro x hx
        rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
        · exact hp x hx
        · rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
          · exact hq x hx
          · exact hr x (by simpa using hx)
      · rw [walkWeight_append,walkWeight_append,walkWeight_reverse]
        linarith [htwo i hi j hj hij]

end MinorFreeSpanners
