import LightEFTSpanners.NativeBasicCoreReduction

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- A genuine k-fold forest packing on original native identities: each
member is a native forest, the members are disjoint, and every original pair
with threshold2k is joined in every member. There is no construction premise. -/
def HasNativeForestPacking (G : Graph V E) (k : ℕ) : Prop :=
  ∃ A : Fin k → Set E,(∀ c,A c⊆G.edgeSet ∧
    ∀ e∈(G.restrict (A c)).edgeSet,(G.restrict (A c)).IsBridge e) ∧
    Pairwise (fun c d => Disjoint (A c) (A d)) ∧
    ∀ c (x y : G.vertexSet),FaultConnected G (2*k) x y →
      (G.restrict (A c)).toSimpleGraph.Reachable x y

omit [Fintype E] in
/-- Empty and singleton ambient domains need no selected edge identities. -/
theorem forestPacking_of_subsingleton [Subsingleton V] (G : Graph V E) (k : ℕ) :
    HasNativeForestPacking G k := by
  refine ⟨fun _ => ∅,?_,?_,?_⟩
  · intro c; exact ⟨Set.empty_subset _,by simp⟩
  · intro c d _; simp
  · intro c x y _; have h : x=y := Subsingleton.elim _ _; subst y; exact Reachable.rfl

/-- When the entire actual graph is one2k-island, the previously proved
native partition criterion constructs the required spanning-tree packing. -/
theorem forestPacking_of_all_pairs [Fintype V] (G : Graph V E) (k : ℕ)
    (hne : G.vertexSet.Nonempty)
    (hc : ∀ x y : G.vertexSet,FaultConnected G (2*k) x y) :
    HasNativeForestPacking G k := by
  classical
  let K : Finset V := G.vertexSet.toFinset
  have hk : (K:Set V)=G.vertexSet := Set.coe_toFinset _
  have hK : K.Nonempty := by simpa [K] using hne
  have hsmall : (G.edgeCut (K:Set V)).toFinset.card≤2*k := by
    have he : G.edgeCut G.vertexSet=∅ := by
      ext e
      constructor
      · rintro ⟨u,v,h,_,hv⟩; exact hv h.right_mem
      · simp
    simp [hk,he]
  have hmin (S : Finset V) (hS : S⊂K) (hn : S.Nonempty) :
      2*k≤(G.edgeCut (S:Set V)).toFinset.card := by
    obtain ⟨x,hx⟩ := hn
    obtain ⟨y,hy,hyS⟩ := Finset.exists_of_ssubset hS
    have hxG : x∈G.vertexSet := by rw [←hk]; exact hS.subset hx
    have hyG : y∈G.vertexSet := by rw [←hk]; exact hy
    exact faultConnected_le_cut G (hc ⟨x,hxG⟩ ⟨y,hyG⟩) (S:Set V) hx hyS
  obtain ⟨A,hA,hd⟩ := exists_native_minimal_core_trees G K k hK (by rw [hk]) hsmall hmin
  have hg : G.induce (K:Set V)=G := by rw [hk,Graph.induce_vertexSet]
  have hAc (c : Fin k) : A c⊆G.edgeSet ∧
      (∀ e∈(G.restrict (A c)).edgeSet,(G.restrict (A c)).IsBridge e) ∧
      (G.restrict (A c)).toSimpleGraph.Connected := by
    have h := hA c
    simp only [hg] at h
    exact ⟨h.1,h.2.1,(congrArg (fun H : Graph V E =>
      (H.restrict (A c)).toSimpleGraph.Connected) hg).mp (hA c).2.2.1⟩
  exact ⟨A,fun c => ⟨(hAc c).1,(hAc c).2.1⟩,hd,
    fun c x y _ => (hAc c).2.2.preconnected x y⟩
end LightEFTSpanners.EvenSplitting
