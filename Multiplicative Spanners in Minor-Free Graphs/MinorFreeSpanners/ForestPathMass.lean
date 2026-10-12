import MinorFreeSpanners.TreePathBranchWitness

/-! An actual maximum-mass simple path inside a finite forest vertex set.
The maximum ranges over real paths, with every path vertex charged once. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

noncomputable def pathMass {V : Type*} {G : SimpleGraph V} (d : V → ℝ)
    {x y : V} (p : G.Walk x y) : ℝ := by
  classical
  exact ∑ v∈p.support.toFinset,d v

 theorem exists_max_mass_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hne : S.Nonempty)
    (d : V → ℝ) :
    ∃ x∈S, ∃ y∈S, ∃ p : G.Walk x y, p.IsPath ∧
      (∀ z∈p.support,z∈S) ∧
      ∀ a b, ∀ q : G.Walk a b, q.IsPath →
        (∀ z∈q.support,z∈S) → pathMass d q ≤ pathMass d p := by
  classical
  let : ∀ x y : V, Subsingleton (G.Path x y) := hG.subsingleton_path
  let P := Σ x : V, Σ y : V, G.Path x y
  let : Fintype P := Fintype.ofFinite P
  let candidates : Finset P := Finset.univ.filter fun q =>
    ∀ z∈q.2.2.val.support,z∈S
  obtain ⟨v,hv⟩ := hne
  have hn : candidates.Nonempty := by
    refine ⟨⟨v,v,⟨.nil,Walk.IsPath.nil⟩⟩,?_⟩
    simp [candidates,hv]
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image candidates (fun q => pathMass d q.2.2.val) hn
  have hs := (Finset.mem_filter.mp hp).2
  refine ⟨p.1,hs _ p.2.2.val.start_mem_support,p.2.1,
    hs _ p.2.2.val.end_mem_support,p.2.2.val,p.2.2.property,hs,?_⟩
  intro a b q hq hqs
  exact hmax ⟨a,b,⟨q,hq⟩⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqs⟩)

 theorem max_mass_path_start_neighbor {V : Type*} (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (d : V → ℝ)
    (hd : ∀ v∈S,0<d v) {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) (hs : ∀ z∈p.support,z∈S)
    (hmax : ∀ a b, ∀ q : G.Walk a b, q.IsPath →
      (∀ z∈q.support,z∈S) → pathMass d q≤pathMass d p)
    {z : V} (hz : z∈S) (hxz : G.Adj x z) : z=p.snd := by
  classical
  apply hG.eq_snd_of_adj_start hp hxz
  by_contra hnot
  have hext := hmax z y (.cons hxz.symm p) (hp.cons hnot)
    (by intro a ha;simp only [Walk.support_cons,List.mem_cons] at ha;rcases ha with rfl|ha;exact hz;exact hs a ha)
  have heq : pathMass d (.cons hxz.symm p)=d z+pathMass d p := by
    simp [pathMass,Walk.support_cons,hnot]
  rw [heq] at hext
  have hpos := hd z hz
  linarith

end MinorFreeSpanners
