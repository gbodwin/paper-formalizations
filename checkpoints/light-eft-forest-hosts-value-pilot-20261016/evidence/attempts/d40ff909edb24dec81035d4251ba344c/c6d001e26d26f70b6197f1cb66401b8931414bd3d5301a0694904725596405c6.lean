import LightEFTSpanners.NativeForestSemantics

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Every actual unordered adjacency edge has one original native identity,
chosen consistently for the unordered pair rather than separately by direction. -/
theorem exists_edge_representative (G : Graph V E) (s : Sym2 G.vertexSet)
    (hs : s∈G.toSimpleGraph.edgeSet) :
    ∃ e : E,∀ u v : G.vertexSet,s=s(u,v) → G.IsLink e u.val v.val := by
  induction s using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨_,e,he⟩ := G.toSimpleGraph.mem_edgeSet.mp hs
    refine ⟨e,?_⟩
    intro u v hp
    rcases Sym2.eq_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact he
    · exact he.symm

noncomputable def edgeRepresentative (G : Graph V E) (s : Sym2 G.vertexSet)
    (hs : s∈G.toSimpleGraph.edgeSet) : E :=
  (exists_edge_representative G s hs).choose

theorem edgeRepresentative_spec (G : Graph V E) (s : Sym2 G.vertexSet)
    (hs : s∈G.toSimpleGraph.edgeSet) (u v : G.vertexSet) (hp : s=s(u,v)) :
    G.IsLink (edgeRepresentative G s hs) u.val v.val :=
  (exists_edge_representative G s hs).choose_spec u v hp

theorem edgeRepresentative_endpoints (G : Graph V E) (s : Sym2 G.vertexSet)
    (hs : s∈G.toSimpleGraph.edgeSet) {u v : G.vertexSet}
    (he : G.IsLink (edgeRepresentative G s hs) u.val v.val) : s=s(u,v) := by
  induction s using Sym2.inductionOn with
  | hf x y =>
    have hxy := edgeRepresentative_spec G s(x,y) hs x y rfl
    rcases hxy.eq_and_eq_or_eq_and_eq he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hx,Subtype.ext hy⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hx,Subtype.ext hy⟩)

theorem edgeRepresentative_mem (G : Graph V E) (s : Sym2 G.vertexSet)
    (hs : s∈G.toSimpleGraph.edgeSet) : edgeRepresentative G s hs∈G.edgeSet := by
  induction s using Sym2.inductionOn with
  | hf x y => exact (edgeRepresentative_spec G s(x,y) hs x y rfl).edge_mem

theorem edgeRepresentative_injective (G : Graph V E) {s t : Sym2 G.vertexSet}
    (hs : s∈G.toSimpleGraph.edgeSet) (ht : t∈G.toSimpleGraph.edgeSet)
    (heq : edgeRepresentative G s hs=edgeRepresentative G t ht) : s=t := by
  induction s using Sym2.inductionOn with
  | hf x y =>
    have he := edgeRepresentative_spec G s(x,y) hs x y rfl
    rw [heq] at he
    exact (edgeRepresentative_endpoints G t ht he).symm

/-- Select exactly one original edge identity per edge of a supplied simple
subgraph, keeping the entire actual native vertex set. -/
def representativeSet (G : Graph V E) (H : SimpleGraph G.vertexSet)
    (hH : H≤G.toSimpleGraph) : Set E :=
  {e | ∃ s : H.edgeSet,e=edgeRepresentative G s.val (SimpleGraph.edgeSet_mono hH s.property)}

abbrev selectNative (G : Graph V E) (H : SimpleGraph G.vertexSet)
    (hH : H≤G.toSimpleGraph) : Graph V E := G.restrict (representativeSet G H hH)

theorem selectNative_simple (G : Graph V E) (H : SimpleGraph G.vertexSet)
    (hH : H≤G.toSimpleGraph) : (selectNative G H hH).Simple := by
  refine {not_isLoopAt := ?_,eq_of_isLink := ?_}
  · intro e x he
    obtain ⟨⟨s,rfl⟩,hlink⟩ := he
    have hp := edgeRepresentative_endpoints G s.val (SimpleGraph.edgeSet_mono hH s.property)
      (u:=⟨x,hlink.left_mem⟩) (v:=⟨x,hlink.right_mem⟩) hlink
    have hs : s(⟨x,hlink.left_mem⟩,⟨x,hlink.right_mem⟩)∈H.edgeSet := hp ▸ s.property
    exact (H.mem_edgeSet.mp hs).ne rfl
  · intro e f x y he hf
    obtain ⟨⟨s,rfl⟩,hse⟩ := he
    obtain ⟨⟨t,rfl⟩,htf⟩ := hf
    have hs := edgeRepresentative_endpoints G s.val (SimpleGraph.edgeSet_mono hH s.property)
      (u:=⟨x,hse.left_mem⟩) (v:=⟨y,hse.right_mem⟩) hse
    have ht := edgeRepresentative_endpoints G t.val (SimpleGraph.edgeSet_mono hH t.property)
      (u:=⟨x,htf.left_mem⟩) (v:=⟨y,htf.right_mem⟩) htf
    have hst : s=t := Subtype.ext (hs.trans ht.symm)
    subst t
    rfl

theorem selectNative_projection (G : Graph V E) (H : SimpleGraph G.vertexSet)
    (hH : H≤G.toSimpleGraph) : (selectNative G H hH).toSimpleGraph=H := by
  ext x y
  constructor
  · rintro ⟨_,e,⟨s,rfl⟩,he⟩
    have hs := edgeRepresentative_endpoints G s.val (SimpleGraph.edgeSet_mono hH s.property) he
    exact H.mem_edgeSet.mp (hs ▸ s.property)
  · intro hxy
    let s : H.edgeSet := ⟨s(x,y),H.mem_edgeSet.mpr hxy⟩
    refine ⟨hxy.ne,edgeRepresentative G s.val (SimpleGraph.edgeSet_mono hH s.property),?_,?_⟩
    · exact ⟨s,rfl⟩
    · exact edgeRepresentative_spec G s.val (SimpleGraph.edgeSet_mono hH s.property) x y rfl

/-- Every native multigraph has an actual spanning forest on its original edge
identities, with the original actual vertex set and exactly the same native
reachability. All retained edges are genuine bridges; loops and parallel cycles
are removed by construction, not silently forgotten before edge selection. -/
theorem exists_native_spanning_forest (G : Graph V E) :
    ∃ F : Set E,F⊆G.edgeSet ∧
      (∀ e∈(G.restrict F).edgeSet,(G.restrict F).IsBridge e) ∧
      (G.restrict F).toSimpleGraph.Reachable=G.toSimpleGraph.Reachable := by
  obtain ⟨H,hH,hacyc,hreach⟩ := G.toSimpleGraph.exists_isAcyclic_reachable_eq_le
  refine ⟨representativeSet G H hH,?_,?_,?_⟩
  · rintro e ⟨s,rfl⟩
    exact edgeRepresentative_mem G s.val (SimpleGraph.edgeSet_mono hH s.property)
  · apply (all_edges_bridge_iff (selectNative G H hH)).mpr
    exact ⟨selectNative_simple G H hH,
      (congrArg (fun K : SimpleGraph G.vertexSet => K.IsAcyclic)
        (selectNative_projection G H hH)).mpr hacyc⟩
  · change (selectNative G H hH).toSimpleGraph.Reachable=G.toSimpleGraph.Reachable
    exact (congrArg (fun K : SimpleGraph G.vertexSet => K.Reachable)
      (selectNative_projection G H hH)).trans hreach
end LightEFTSpanners.MultigraphCuts
