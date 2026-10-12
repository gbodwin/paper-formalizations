import MinorFreeSpanners.ResidualComponents
import MinorFreeSpanners.RootedPathDiameter

/-! The actual coarse absorption graph keeps every residual edge and connects
its chosen boundary ports to one contracted root. A path avoiding that root
is an original residual path in one genuine connected component. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

noncomputable def rootedResidualGraph {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (root : I) (ports : Finset I) : SimpleGraph I where
  Adj x y := x≠y ∧ ((H.Adj x y ∧ x∈R ∧ y∈R) ∨
    (x=root ∧ y∈ports) ∨ (y=root ∧ x∈ports))
  symm := ⟨by
    rintro x y ⟨hne,h | h | h⟩
    · exact ⟨hne.symm,Or.inl ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    · exact ⟨hne.symm,Or.inr (Or.inr h)⟩
    · exact ⟨hne.symm,Or.inr (Or.inl h)⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

 theorem residual_walk_in_block {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (Q : (H.induce (R:Set I)).ConnectedComponent) {x y : I} (p : H.Walk x y)
    (hx : x∈ResidualComponents.block H R Q) (hp : ∀ z∈p.support,z∈R) :
    ∀ z∈p.support,z∈ResidualComponents.block H R Q := by
  induction p with
  | nil => simpa using hx
  | cons h q ih =>
    have hy := ResidualComponents.closed_adj H R Q hx (hp _ (by simp)) h
    have hh := ih hy (fun z hz => hp z (by simp [hz]))
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact hh z hz

 theorem root_avoiding_transfer {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (root : I) (ports : Finset I) {x y : I}
    (p : (rootedResidualGraph H R root ports).Walk x y) (havoid : root∉p.support) :
    ∃ q : H.Walk x y,q.support=p.support ∧ (p.IsPath → q.IsPath) := by
  classical
  have he : ∀ e∈p.edges,e∈H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with | hf a b =>
      have ha := p.fst_mem_support_of_mem_edges he
      have hb := p.snd_mem_support_of_mem_edges he
      have hab : (rootedResidualGraph H R root ports).Adj a b := p.edges_subset_edgeSet he
      rcases hab.2 with hh | hh | hh
      · exact hh.1
      · exact (havoid (hh.1 ▸ ha)).elim
      · exact (havoid (hh.1 ▸ hb)).elim
  exact ⟨p.transfer H he,Walk.support_transfer _ _,fun hp => hp.transfer he⟩

 theorem root_avoiding_component_bound {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (root : I) (ports : Finset I) (d : I → ℝ) (K : ℝ)
    (hcomponent : ∀ Q : (H.induce (R:Set I)).ConnectedComponent,
      ∀ a b,∀ q : H.Walk a b,q.IsPath →
        (∀ i∈q.support,i∈ResidualComponents.block H R Q) → pathMass d q≤K)
    {x y : I} (p : (rootedResidualGraph H R root ports).Walk x y)
    (hp : p.IsPath) (hS : ∀ i∈p.support,i∈insert root R) (havoid : root∉p.support) :
    pathMass d p≤K := by
  classical
  obtain ⟨q,hq,hqp⟩ := root_avoiding_transfer H R root ports p havoid
  have hR : ∀ i∈q.support,i∈R := by
    intro i hi
    have hi' : i∈p.support := hq ▸ hi
    rcases Finset.mem_insert.mp (hS i hi') with he | he
    · exact (havoid (he ▸ hi')).elim
    · exact he
  obtain ⟨Q,hQ⟩ := ResidualComponents.covers H R (hR x q.start_mem_support)
  have hh := hcomponent Q x y q (hqp hp) (residual_walk_in_block H R Q q hQ hR)
  simpa only [pathMass,hq] using hh

end MinorFreeSpanners
