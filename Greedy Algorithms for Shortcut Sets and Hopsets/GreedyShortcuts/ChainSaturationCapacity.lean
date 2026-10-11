import GreedyShortcuts.ChainShortRowCapacity
import GreedyShortcuts.ChainExcessLayers

/-! Exact newly saturated demand capacity for a covered interchain insertion.
The old distance is unrestricted. This is an upper bound, not progress. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem saturating_improvement_labels {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v s t : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d)
    (hst : (s,t) ∈ T.important)
    (hsat : T.distance (insert (u,v) H) s t = T.endpointFloor s t)
    (hdrop : T.distance (insert (u,v) H) s t < T.distance H s t) :
    label T.chains s = some c ∧ label T.chains t = some d := by
  classical
  have hlegal : insert (u,v) H ⊆ candidates T.G := Finset.insert_subset he hH
  have hr := (T.important_spec hst).1
  obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
  have hbad : ¬Allowed (T.graph H s) p := by
    intro hh
    have hb := T.distance_le_walk H hr p hh
    omega
  simp only [Allowed,not_forall] at hbad
  obtain ⟨dart,hmem,hnot⟩ := hbad
  have hstep := hp dart hmem
  have hedge : (dart.fst,dart.snd) = (u,v) := by
    rcases hstep.1 with hg | hh
    · exact (hnot ⟨Or.inl hg,hstep.2⟩).elim
    rcases Finset.mem_union.mp hh with hb | hi
    · exact (hnot ⟨Or.inr (Finset.mem_union_left _ hb),hstep.2⟩).elim
    rcases Finset.mem_insert.mp hi with heq | hmem
    · exact heq
    · exact (hnot ⟨Or.inr (Finset.mem_union_right _ hmem),hstep.2⟩).elim
  have hfst : dart.fst = u := congrArg Prod.fst hedge
  have hsnd : dart.snd = v := congrArg Prod.snd hedge
  have hh := T.saturated_dart_labels hlegal p hp (by omega) dart hmem
    (by simpa only [hfst] using hu) (by simpa only [hsnd] using hv) hcd
  exact hh

/-- A legal covered interchain insertion can newly saturate at most one
important demand per actual source vertex on its tail chain. -/
theorem saturation_drop_le_tail_size {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d) :
    (T.unsaturated H).card-(T.unsaturated (insert (u,v) H)).card ≤
      (T.chains c).length := by
  classical
  let B := T.unsaturated H \ T.unsaturated (insert (u,v) H)
  have hsub : B ⊆ (T.chains c).support.image (fun s => (s,entry T.chains s d)) := by
    intro st hs
    obtain ⟨hOld,hNot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hOld
    have hnew : T.distance (insert (u,v) H) st.1 st.2 = T.endpointFloor st.1 st.2 := by
      have hlo := T.endpointFloor_le_distance (insert (u,v) H) (T.important_spec hp).1
      have hn : ¬ T.endpointFloor st.1 st.2 < T.distance (insert (u,v) H) st.1 st.2 := by
        intro hh
        exact hNot (Finset.mem_filter.mpr ⟨hp,hh⟩)
      omega
    have hlabels := T.saturating_improvement_labels hH he hu hv hcd hp hnew (by omega)
    have hi := (T.important_spec hp).2
    have ht : entry T.chains st.1 d = st.2 := by
      simpa only [first,hlabels.2] using hi
    exact Finset.mem_image.mpr ⟨st.1,mem_of_label T.chains hlabels.1,Prod.ext rfl ht⟩
  have hB : B.card = (T.unsaturated H).card-(T.unsaturated (insert (u,v) H)).card :=
    Finset.card_sdiff_of_subset (T.unsaturated_antitone (Finset.subset_insert _ _))
  rw [←hB]
  calc
    _ ≤ ((T.chains c).support.image (fun s => (s,entry T.chains s d))).card := Finset.card_le_card hsub
    _ ≤ (T.chains c).support.card := Finset.card_image_le
    _ = _ := ChainUnion.Chain.support_card _

/-- After deleting the endpoint-adjacent excess layer, all but at most the
actual tail-chain size of an insertion's raw marginal remains. -/
theorem raw_drop_le_tail_add_layer {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d) :
    T.potential H-T.potential (insert (u,v) H) ≤ (T.chains c).length+
      (T.layerPotential H 1-T.layerPotential (insert (u,v) H) 1) := by
  rw [T.raw_drop_eq_saturation_add_layer (Finset.subset_insert _ _)]
  exact Nat.add_le_add_right (T.saturation_drop_le_tail_size hH he hu hv hcd) _

/-- Any insertion whose raw marginal dominates twice its tail-chain size
retains at least half of that marginal above the first excess layer. -/
theorem half_raw_drop_le_layer {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d)
    (hlarge : 2*(T.chains c).length ≤ T.potential H-T.potential (insert (u,v) H)) :
    T.potential H-T.potential (insert (u,v) H) ≤
      2*(T.layerPotential H 1-T.layerPotential (insert (u,v) H) 1) := by
  have h := T.raw_drop_le_tail_add_layer hH he hu hv hcd
  omega

end GreedyShortcuts.ChainDistance.Context
