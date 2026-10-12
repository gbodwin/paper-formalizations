import MinorFreeSpanners.ResidualComponents
import MinorFreeSpanners.PathMassTransport

/-! Graph-isomorphic residual domains transport their actual component
spanning paths with identical distinct-vertex mass and simplicity. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ResidualComponents
variable {I J : Type*} {H : SimpleGraph I} {K : SimpleGraph J}

 theorem iso_block (R : Finset I) (S : Finset J)
    (e : H.induce (R:Set I) ≃g K.induce (S:Set J))
    (t : (H.induce (R:Set I)).ConnectedComponent) :
    block K S (e.connectedComponentEquiv t)=t.supp.toFinset.image (fun i => (e i).val) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyS,hy⟩ := (mem_block K S _ y).mp hy
    have hx : e.symm ⟨y,hyS⟩∈t.supp :=
      ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr hy
    exact Finset.mem_image.mpr ⟨e.symm ⟨y,hyS⟩,Set.mem_toFinset.mpr hx,
      congrArg Subtype.val (e.apply_symm_apply ⟨y,hyS⟩)⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact (mem_block K S _ _).mpr ⟨(e x).property,
      (t.isoEquivSupp e ⟨x,Set.mem_toFinset.mp hx⟩).property⟩

 theorem spanning_path_transport (R : Finset I) (S : Finset J)
    (e : H.induce (R:Set I) ≃g K.induce (S:Set J))
    (d : I → ℝ) (d' : J → ℝ) (hd : ∀ i,d' (e i).val=d i.val)
    (t : (H.induce (R:Set I)).ConnectedComponent)
    {x y : I} (p : H.Walk x y) (hp : p.IsPath) (hs : p.support.toFinset=block H R t) :
    ∃ x' y',∃ q : K.Walk x' y',q.IsPath ∧
      q.support.toFinset=block K S (e.connectedComponentEquiv t) ∧ pathMass d' q=pathMass d p := by
  classical
  have hpR : ∀ i∈p.support,i∈(R:Set I) := fun i hi =>
    subset H R t (hs ▸ List.mem_toFinset.mpr hi)
  let p0 := p.induce (R:Set I) hpR
  let f : H.induce (R:Set I) →g K := (Embedding.induce (G:=K) (S:Set J)).toHom.comp e.toHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let q := p0.map f
  have hp0 : p0.IsPath := by
    apply Walk.IsPath.of_map (f:=(Embedding.induce (G:=H) (R:Set I)).toHom)
    change ((p.induce (R:Set I) hpR).map (Embedding.induce (R:Set I)).toHom).IsPath
    rw [Walk.map_induce]
    exact hp
  have hp0supp : p0.support.toFinset=t.supp.toFinset := by
    ext i
    simp only [List.mem_toFinset,Set.mem_toFinset]
    have hh : i.val∈p.support ↔ i∈p0.support := by
      change i.val∈p.support ↔ i∈(p.induce (R:Set I) hpR).support
      rw [Walk.support_induce]
      exact (List.mem_attachWith hpR i).symm
    rw [←hh,←List.mem_toFinset,hs]
    exact ⟨fun hi => ((mem_block H R t i.val).mp hi).choose_spec,
      fun hi => (mem_block H R t i.val).mpr ⟨i.property,hi⟩⟩
  have hmass := pathMass_map f hf d' p0
  have hd' : (fun i => d' (f i))=(fun i : (R:Set I) => d i.val) := by
    funext i
    exact hd i
  rw [hd'] at hmass
  refine ⟨_,_,q,hp0.map hf,?_,hmass.trans (pathMass_induce (R:Set I) d p hpR)⟩
  change (p0.map f).support.toFinset=_
  have himage : (List.map (⇑f) p0.support).toFinset=p0.support.toFinset.image f := by
    ext j
    simp
  rw [Walk.support_map,himage,hp0supp,iso_block R S e t]
  rfl

 theorem all_spanning_paths_transport (R : Finset I) (S : Finset J)
    (e : H.induce (R:Set I) ≃g K.induce (S:Set J))
    (d : I → ℝ) (d' : J → ℝ) (hd : ∀ i,d' (e i).val=d i.val) (L : ℝ)
    (hpath : ∀ t : (H.induce (R:Set I)).ConnectedComponent,
      ∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=block H R t ∧ L≤pathMass d p) :
    ∀ t : (K.induce (S:Set J)).ConnectedComponent,
      ∃ x y,∃ p : K.Walk x y,p.IsPath ∧ p.support.toFinset=block K S t ∧ L≤pathMass d' p := by
  intro t
  obtain ⟨x,y,p,hp,hs,hm⟩ := hpath (e.connectedComponentEquiv.symm t)
  obtain ⟨a,b,q,hq,hqs,he⟩ := spanning_path_transport R S e d d' hd _ p hp hs
  rw [e.connectedComponentEquiv.apply_symm_apply] at hqs
  exact ⟨a,b,q,hq,hqs,he.symm ▸ hm⟩

end ResidualComponents
end MinorFreeSpanners
