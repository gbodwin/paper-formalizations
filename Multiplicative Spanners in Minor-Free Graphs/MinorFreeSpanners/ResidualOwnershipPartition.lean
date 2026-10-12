import MinorFreeSpanners.ResidualBoundaryOwnership

/-! Every residual connected component receives one root through an actual
boundary edge. The resulting fibers form a covering, disjoint partition and
retain every residual component whole. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

structure ResidualOwnership {I : Type*} [Fintype I] (H : SimpleGraph I) (roots : Finset I) where
  owner : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent → {r // r∈roots}
  port : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent → I
  port_mem : ∀ Q,port Q∈ResidualComponents.block H (Finset.univ\roots) Q
  adjacent : ∀ Q,H.Adj (owner Q).val (port Q)

 theorem exists_residual_ownership {I : Type*} [Fintype I] (H : SimpleGraph I)
    (hconn : ConnectedWithin H Finset.univ) (roots : Finset I) (hne : roots.Nonempty) :
    Nonempty (ResidualOwnership H roots) := by
  classical
  have hh (Q : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :=
    residual_component_boundary H hconn roots hne Q
  choose port hp owner ho hedge using hh
  exact ⟨⟨fun Q => ⟨owner Q,ho Q⟩,port,hp,fun Q => (hedge Q).symm⟩⟩

namespace ResidualOwnership
variable {I : Type*} [Fintype I] {H : SimpleGraph I} {roots : Finset I}

noncomputable def components (O : ResidualOwnership H roots) (r : {r // r∈roots}) :
    Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent := by
  classical
  letI := Fintype.ofFinite (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent
  exact Finset.univ.filter fun Q => O.owner Q=r

noncomputable def absorbed (O : ResidualOwnership H roots) (r : {r // r∈roots}) : Finset I :=
  (O.components r).biUnion (ResidualComponents.block H (Finset.univ\roots))

noncomputable def filled (O : ResidualOwnership H roots) (r : {r // r∈roots}) : Finset I :=
  insert r.val (O.absorbed r)

 theorem mem_absorbed (O : ResidualOwnership H roots) (r : {r // r∈roots}) (x : I) :
    x∈O.absorbed r ↔ ∃ Q,O.owner Q=r ∧ x∈ResidualComponents.block H (Finset.univ\roots) Q := by
  classical
  simp [absorbed,components]

 theorem absorbed_residual (O : ResidualOwnership H roots) (r : {r // r∈roots}) :
    O.absorbed r⊆Finset.univ\roots := by
  intro x hx
  obtain ⟨Q,_,hx⟩ := (O.mem_absorbed r x).mp hx
  exact ResidualComponents.subset H _ Q hx

 theorem root_not_absorbed (O : ResidualOwnership H roots) (r s : {r // r∈roots}) :
    r.val∉O.absorbed s := by
  intro h
  exact (Finset.mem_sdiff.mp (O.absorbed_residual s h)).2 r.property

 theorem absorbed_disjoint (O : ResidualOwnership H roots) (r s : {r // r∈roots}) (hrs : r≠s) :
    Disjoint (O.absorbed r) (O.absorbed s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨Q,hQ,hx⟩ := (O.mem_absorbed r x).mp hx
  obtain ⟨T,hT,hy⟩ := (O.mem_absorbed s x).mp hy
  by_cases he : Q=T
  · exact hrs (hQ.symm.trans (he ▸ hT))
  · exact Finset.disjoint_left.mp (ResidualComponents.disjoint H _ Q T he) hx hy

 theorem filled_disjoint (O : ResidualOwnership H roots) (r s : {r // r∈roots}) (hrs : r≠s) :
    Disjoint (O.filled r) (O.filled s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rcases Finset.mem_insert.mp hy with he | he
    · exact hrs (Subtype.ext he)
    · exact O.root_not_absorbed r s he
  · rcases Finset.mem_insert.mp hy with he | he
    · subst x; exact O.root_not_absorbed s r hx
    · exact Finset.disjoint_left.mp (O.absorbed_disjoint r s hrs) hx he

 theorem filled_covers (O : ResidualOwnership H roots) (x : I) :
    ∃ r : {r // r∈roots},x∈O.filled r := by
  classical
  by_cases hx : x∈roots
  · exact ⟨⟨x,hx⟩,Finset.mem_insert_self _ _⟩
  obtain ⟨Q,hQ⟩ := ResidualComponents.covers H (Finset.univ\roots)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩)
  exact ⟨O.owner Q,Finset.mem_insert_of_mem ((O.mem_absorbed _ x).mpr ⟨Q,rfl,hQ⟩)⟩

end ResidualOwnership
end MinorFreeSpanners
