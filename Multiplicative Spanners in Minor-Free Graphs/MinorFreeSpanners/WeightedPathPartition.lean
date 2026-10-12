import MinorFreeSpanners.WeightedDisjointPathSplit

/-! Finite greedy segmentation of a genuine simple path. The blocks partition
its ORIGINAL ordered support, have controlled effective mass, and each retain
a real simple subpath. A short terminal remainder is never discarded. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def WeightedPathBlock {I : Type*} (H : SimpleGraph I) (d : I → ℝ)
    (L U : ℝ) (nodes : List I) : Prop :=
  ∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support=nodes ∧
    L≤pathMass d p ∧ pathMass d p<U

 theorem exists_weighted_path_partition {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (D L : ℝ) (hD : 0≤D) (hL : 0<L)
    {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    (hd : ∀ i∈p.support,d i≤D) (hm : L≤pathMass d p) :
    ∃ blocks : List (List I),blocks.flatten=p.support ∧
      ∀ nodes∈blocks,WeightedPathBlock H d L (2*L+D) nodes := by
  classical
  suffices ∀ n : ℕ,∀ x y,∀ p : H.Walk x y,p.length≤n → p.IsPath →
      (∀ i∈p.support,d i≤D) → L≤pathMass d p →
      ∃ blocks : List (List I),blocks.flatten=p.support ∧
        ∀ nodes∈blocks,WeightedPathBlock H d L (2*L+D) nodes from
    this p.length x y p le_rfl hp hd hm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y p hlen hp hd hm
    by_cases hshort : pathMass d p<2*L+D
    · refine ⟨[p.support],by simp,?_⟩
      intro nodes hn
      have he : nodes=p.support := by simpa using hn
      subst nodes
      exact ⟨x,y,p,hp,rfl,hm,hshort⟩
    · obtain ⟨u,v,q,r,h,he,hq,hr,hs,_,hlo,hhi,hrmass,hrlen⟩ :=
        exists_weighted_disjoint_path_split d D L hD hL p hp hd (le_of_not_gt hshort)
      have hrd : ∀ i∈r.support,d i≤D := by
        intro i hi
        exact hd i (by rw [hs];exact List.mem_append_right _ hi)
      obtain ⟨blocks,hblocks,hgood⟩ := ih r.length (by omega) v y r le_rfl hr hrd hrmass
      refine ⟨q.support::blocks,?_,?_⟩
      · simpa only [List.flatten_cons,hblocks] using hs.symm
      · intro nodes hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact ⟨x,u,q,hq,rfl,hlo,by linarith⟩
        · exact hgood nodes hn

end MinorFreeSpanners
