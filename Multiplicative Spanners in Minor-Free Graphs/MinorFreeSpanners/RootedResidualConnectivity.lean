import MinorFreeSpanners.RootedResidualGraph

/-! Whole selected residual components attach through their actual chosen
ports. This proves connectivity of the contracted-root graph internally. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem residual_walk_transfer {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (root : I) (ports : Finset I) {x y : I} (p : H.Walk x y)
    (hp : ∀ z∈p.support,z∈R) :
    ∃ q : (rootedResidualGraph H R root ports).Walk x y,q.support=p.support := by
  classical
  have he : ∀ e∈p.edges,e∈(rootedResidualGraph H R root ports).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with | hf a b =>
      have hab : H.Adj a b := p.edges_subset_edgeSet he
      exact ⟨hab.ne,Or.inl ⟨hab,hp a (p.fst_mem_support_of_mem_edges he),
        hp b (p.snd_mem_support_of_mem_edges he)⟩⟩
  exact ⟨p.transfer _ he,Walk.support_transfer _ _⟩

 theorem rooted_residual_connected {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (root : I) (hr : root∉R) (ports : Finset I) (hports : ports⊆R)
    (hreach : ∀ x∈R,∃ y∈ports,∃ p : H.Walk x y,∀ z∈p.support,z∈R) :
    ConnectedWithin (rootedResidualGraph H R root ports) (insert root R) := by
  classical
  have toRoot (x : I) (hx : x∈insert root R) :
      ∃ p : (rootedResidualGraph H R root ports).Walk x root,
        ∀ z∈p.support,z∈insert root R := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨.nil,by simp⟩
    obtain ⟨y,hy,p,hp⟩ := hreach x hx
    obtain ⟨q,hq⟩ := residual_walk_transfer H R root ports p hp
    have hyn : y≠root := by intro he; exact hr (he ▸ hports hy)
    have hedge : (rootedResidualGraph H R root ports).Adj y root :=
      ⟨hyn,Or.inr (Or.inr ⟨rfl,hy⟩)⟩
    refine ⟨q.append (.cons hedge .nil),?_⟩
    intro z hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact Finset.mem_insert_of_mem (hp z (hq ▸ hz))
    · simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_insert_of_mem (hports hy)
      · exact Finset.mem_insert_self _ _
  intro x hx y hy
  obtain ⟨p,hp⟩ := toRoot x hx
  obtain ⟨q,hq⟩ := toRoot y hy
  refine ⟨p.append q.reverse,?_⟩
  intro z hz
  rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact hp z hz
  · exact hq z (by simpa using hz)

 theorem components_reach_chosen_ports {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (Q : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ c∈Q,port c∈ResidualComponents.block H R c) :
    let S := Q.biUnion (ResidualComponents.block H R)
    let P := Q.image port
    P⊆S ∧ ∀ x∈S,∃ y∈P,∃ p : H.Walk x y,∀ z∈p.support,z∈S := by
  classical
  dsimp
  constructor
  · intro y hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨c,hc,hport c hc⟩
  · intro x hx
    obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p,hp⟩ := ResidualComponents.connected H R c x hx (port c) (hport c hc)
    exact ⟨port c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,p,
      fun z hz => Finset.mem_biUnion.mpr ⟨c,hc,hp z hz⟩⟩

end MinorFreeSpanners
