import GreedyShortcuts.ChainCoalescingRootSuffix
import GreedyShortcuts.ChainEntryLevels

/-! SOURCE ONLY, UNCOMPILED. Actual requested-rank important anchors of an
unchanged attained ROOT minimum, including uncovered ROOT's first level.
Physical position is not chain rank. No corridor/owner/forcing properties
are assumed as structure fields, and no original minimum is favorably retied. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- SAME-source prefix minimum at any physical index of the supplied walk.
No minimum in the forward-rebased source is inferred. -/
theorem root_minimum_prefix_price {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root W : V} (P : DWalk root W)
    (hP : Allowed (T.graph H root) P)
    (hmin : T.count P=T.distance H root W) (i : ℕ) :
    T.count (P.take i)=T.distance H root (P.getVert i) := by
  exact T.minimum_take hH P hP hmin i

/-- Every positive level actually present on the walk gives an important
prefix endpoint. The initial covered marker is handled at position zero;
all other levels use an actual first-increase dart of the SAME walk. -/
theorem exists_positive_important_corridor_prefix {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root W : V} (P : DWalk root W)
    (hP : Allowed (T.graph H root) P) (c : ℕ)
    (hc : 1≤c) (hcP : c≤T.count P) :
    ∃ i,i≤P.length ∧ T.count (P.take i)=c ∧
      (root,P.getVert i) ∈ T.important ∧
      (c≤T.rootStartMarker root → i=0) ∧
      (T.rootStartMarker root<c → 0 < i) := by
  classical
  by_cases hstart : c≤T.rootStartMarker root
  · have hm : T.rootStartMarker root≤1 := by
      cases hlabel : label T.chains root <;> simp [rootStartMarker,hlabel]
    have hec : c=1 := by omega
    have hmone : T.rootStartMarker root=1 := by omega
    have hcovered : label T.chains root≠none := by
      intro he
      have hz : T.rootStartMarker root=0 := by simp [rootStartMarker,he]
      omega
    obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hcovered
    have hip : (root,root) ∈ T.important := by
      simpa only [T.first_self root] using
        T.first_important (reachable_refl T.G root) hd
    refine ⟨0,Nat.zero_le _,?_,?_,fun _ => rfl,?_⟩
    · simp [count,chainSet,hd,hec]
    · simpa only [Walk.getVert_zero] using hip
    · intro hh
      omega
  · have hstart' : T.rootStartMarker root<c := by omega
    obtain ⟨i,hil,hcount,hip⟩ := T.exists_entry_level hH P hP c (by omega) hcP
    have hi0 : 0 < i := by
      by_contra hn
      have he : i=0 := by omega
      have hzero : T.count (P.take 0)=T.rootStartMarker root := by
        simp [count,chainSet,rootStartMarker]
      rw [he,hzero] at hcount
      omega
    exact ⟨i,hil,hcount,hip,(fun hh => by omega),fun _ => hi0⟩

/-- Important targets have positive native rank; rank zero is not invented
as an important anchor when ROOT is uncovered. No height assumption needed. -/
theorem important_root_rank_positive (H : Finset (V × V)) {root W : V}
    (hW : (root,W) ∈ T.important) : 1≤T.distance H root W := by
  classical
  obtain ⟨P,_hP,hmin⟩ := T.distance_spec H (T.important_spec hW).1
  obtain ⟨d,hd⟩ := T.important_covered hW
  have hm : d ∈ T.chainSet P :=
    (T.mem_chainSet P d).mpr ⟨W,P.end_mem_support,hd⟩
  have hp : 1≤T.count P := Finset.one_le_card.mpr ⟨d,hm⟩
  omega

/-- The actual initial rank is exactly the optional covered ROOT marker.
This preserves uncovered rank zero and covered rank one without pretending
that an uncovered ROOT is an important anchor. -/
theorem root_self_rank_eq_marker {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) (root : V) :
    T.distance H root root=T.rootStartMarker root := by
  obtain ⟨P,hP,hmin⟩ := T.distance_spec H (reachable_refl T.G root)
  have hc := T.fixed_root_count_eq_marker_transitions hH P
    (reachable_refl T.G root) hP
  have hnil : T.count (.nil : DWalk root root)=T.rootStartMarker root := by
    simp [count,chainSet,rootStartMarker]
  have hu := T.distance_le_walk H (reachable_refl T.G root)
    (.nil : DWalk root root) (allowed_nil _ _)
  omega

/-- Requested-rank anchor of ANY already fixed admitted ROOT minimum.
At c=rank(W) choose the REAL endpoint explicitly. Only c<rank(W) implies
an earlier physical position and anchor!=W. Uncovered ROOT's c=1 is not lost.
All rank/count and reachability conclusions are derived from P. -/
theorem exists_root_minimum_corridor_anchor {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root W : V}
    (hW : (root,W) ∈ T.important) (P : DWalk root W)
    (hP : Allowed (T.graph H root) P)
    (hmin : T.count P=T.distance H root W) (c : ℕ)
    (hc : 1≤c) (hcR : c≤T.distance H root W) :
    ∃ i,i≤P.length ∧ T.count (P.take i)=c ∧
      (root,P.getVert i) ∈ T.important ∧
      T.distance H root (P.getVert i)=c ∧
      Reachable T.G (P.getVert i) W ∧
      (c=T.distance H root W → i=P.length ∧ P.getVert i=W) ∧
      (c<T.distance H root W → i<P.length ∧ P.getVert i≠W) ∧
      (c<T.distance H root W → c≤T.rootStartMarker root → i=0) ∧
      (T.rootStartMarker root<c → 0 < i) := by
  classical
  have hend : T.count (P.take P.length)=T.count P := by
    unfold count
    rw [Walk.take_of_length_le (Nat.le_refl _),T.chainSet_copy]
  have hzero : T.count (P.take 0)=T.rootStartMarker root := by
    simp [count,chainSet,rootStartMarker]
  by_cases hterminal : c=T.distance H root W
  · have hcount : T.count (P.take P.length)=c := by omega
    refine ⟨P.length,le_rfl,hcount,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Walk.getVert_length] using hW
    · simpa only [Walk.getVert_length] using hterminal.symm
    · simpa only [Walk.getVert_length] using reachable_refl T.G W
    · intro _
      exact ⟨rfl,P.getVert_length⟩
    · intro hstrict
      omega
    · intro hstrict _
      omega
    · intro hstart
      by_contra hn
      have he : P.length=0 := by omega
      rw [he,hzero] at hcount
      omega
  · have hstrict : c<T.distance H root W := by omega
    obtain ⟨i,hil,hcount,hip,hinitial,hafter⟩ :=
      T.exists_positive_important_corridor_prefix hH P hP c hc (by omega)
    have hprice : T.distance H root (P.getVert i)=c :=
      (T.root_minimum_prefix_price hH P hP hmin i).symm.trans hcount
    have hreach : Reachable T.G (P.getVert i) W :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨P.drop i,allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk hP (P.isSubwalk_drop i))⟩
    have hilt : i<P.length := by
      by_contra hn
      have he : i=P.length := by omega
      rw [he,hend] at hcount
      omega
    have hne : P.getVert i≠W := by
      intro he
      rw [he] at hprice
      omega
    exact ⟨i,hil,hcount,hip,hprice,hreach,
      (fun he => (hterminal he).elim),fun _ => ⟨hilt,hne⟩,
      fun _ => hinitial,hafter⟩

/-- The actual normalized endpoint supplies important W through its REAL
cone membership. The supplied corridor P is not reselected or retied. -/
theorem normalized_root_corridor_anchor {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root W : V}
    (hW : T.RootConeMaximizer H root W W) (P : DWalk root W)
    (hP : Allowed (T.graph H root) P)
    (hmin : T.count P=T.distance H root W) (c : ℕ)
    (hc : 1≤c) (hcR : c≤T.distance H root W) :
    ∃ i,i≤P.length ∧ T.count (P.take i)=c ∧
      (root,P.getVert i) ∈ T.important ∧
      T.distance H root (P.getVert i)=c ∧
      Reachable T.G (P.getVert i) W ∧
      (c=T.distance H root W → i=P.length ∧ P.getVert i=W) ∧
      (c<T.distance H root W → i<P.length ∧ P.getVert i≠W) ∧
      (c<T.distance H root W → c≤T.rootStartMarker root → i=0) ∧
      (T.rootStartMarker root<c → 0 < i) := by
  exact T.exists_root_minimum_corridor_anchor hH
    (T.mem_rootHeadCone_iff.mp hW.1).1 P hP hmin c hc hcR

/-- If a corridor has not yet been fixed, actual native attainment chooses
ONE ROOT minimum and all requested anchors are extracted from THAT walk.
The preceding theorem applies instead when the original corridor is fixed. -/
theorem exists_normalized_root_minimum_corridor {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root W : V}
    (hW : T.RootConeMaximizer H root W W) :
    ∃ P : DWalk root W,Allowed (T.graph H root) P ∧
      T.count P=T.distance H root W ∧ P.IsPath ∧
      ∀ c : ℕ,1≤c → c≤T.distance H root W →
        ∃ i,i≤P.length ∧ T.count (P.take i)=c ∧
          (root,P.getVert i) ∈ T.important ∧
          T.distance H root (P.getVert i)=c ∧
          Reachable T.G (P.getVert i) W ∧
          (c=T.distance H root W → i=P.length ∧ P.getVert i=W) ∧
          (c<T.distance H root W → i<P.length ∧ P.getVert i≠W) ∧
          (c<T.distance H root W → c≤T.rootStartMarker root → i=0) ∧
          (T.rootStartMarker root<c → 0 < i) := by
  have hip := (T.mem_rootHeadCone_iff.mp hW.1).1
  obtain ⟨P,hP,hmin⟩ := T.distance_spec H (T.important_spec hip).1
  exact ⟨P,hP,hmin,allowed_isPath (T.graph_acyclic hH root) P hP,
    fun c hc hcR => T.normalized_root_corridor_anchor hH hW P hP hmin c hc hcR⟩

end GreedyShortcuts.ChainDistance.Context
