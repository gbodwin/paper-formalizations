import GreedyShortcuts.ChainCounting

/-! The immutable endpoint-label floor of normalized distance.
A demand already at this floor cannot improve after further insertions. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def endpointFloor (s t : V) : ℕ :=
  ((label T.chains s).toFinset ∪ (label T.chains t).toFinset).card

theorem endpointFloor_le_two (s t : V) : T.endpointFloor s t ≤ 2 := by
  have h := Finset.card_union_le (label T.chains s).toFinset (label T.chains t).toFinset
  have hs : (label T.chains s).toFinset.card ≤ 1 := by cases label T.chains s <;> simp
  have ht : (label T.chains t).toFinset.card ≤ 1 := by cases label T.chains t <;> simp
  exact h.trans (by omega)

/-- Every real walk contains its two endpoint labels, whether or not it is
valid or minimum. Equality of endpoint labels is counted only once. -/
theorem endpointFloor_le_count {s t : V} (p : DWalk s t) :
    T.endpointFloor s t ≤ T.count p := by
  classical
  apply Finset.card_le_card
  intro c hc
  rcases Finset.mem_union.mp hc with hs | ht
  · exact (T.mem_chainSet p c).mpr ⟨s,p.start_mem_support,by simpa using hs⟩
  · exact (T.mem_chainSet p c).mpr ⟨t,p.end_mem_support,by simpa using ht⟩

theorem endpointFloor_le_distance (H : Finset (V × V)) {s t : V}
    (hr : Reachable T.G s t) : T.endpointFloor s t ≤ T.distance H s t := by
  obtain ⟨p,_,hp⟩ := T.distance_spec H hr
  exact (T.endpointFloor_le_count p).trans_eq hp

theorem endpointFloor_eq_two {s t : V} {c d : I}
    (hs : label T.chains s = some c) (ht : label T.chains t = some d) (hne : c ≠ d) :
    T.endpointFloor s t = 2 := by
  classical
  simp [endpointFloor,hs,ht,hne]

/-- A saturated demand stays saturated under any larger shortcut state.
This does not assert that every low-cost demand is saturated. -/
theorem saturated_mono {H J : Finset (V × V)} (hHJ : H ⊆ J) {s t : V}
    (hr : Reachable T.G s t) (hsat : T.distance H s t = T.endpointFloor s t) :
    T.distance J s t = T.endpointFloor s t :=
  Nat.le_antisymm ((T.distance_antitone s t hHJ).trans_eq hsat)
    (T.endpointFloor_le_distance J hr)

/-- Directly repaired important demands on distinct covered chains attain
the absolute endpoint floor, not merely an upper bound of two. -/
theorem direct_repair_saturated (H : Finset (V × V)) {s t : V}
    (hst : (s,t) ∈ T.important) {c d : I}
    (hs : label T.chains s = some c) (ht : label T.chains t = some d) (hne : c ≠ d) :
    T.distance (insert (s,t) H) s t = T.endpointFloor s t := by
  rw [T.endpointFloor_eq_two hs ht hne]
  have hlow := T.endpointFloor_le_distance (insert (s,t) H) (T.important_spec hst).1
  rw [T.endpointFloor_eq_two hs ht hne] at hlow
  exact Nat.le_antisymm (T.direct_repair H hst) hlow

end GreedyShortcuts.ChainDistance.Context
