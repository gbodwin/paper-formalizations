import GreedyShortcuts.ChainDistance

/-! The actual source/earliest-entry demand set used by chain Algorithm 2.
Every demand has a legal direct repair with normalized cost at most two. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainUnion ChainFirst NormalizedReachability
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def active : Finset (V × I) := by
  classical
  exact Finset.univ.filter (fun sc => (reachableIndices T.chains sc.1 sc.2).Nonempty)

noncomputable def important : Finset (V × V) :=
  T.active.image (fun sc => (sc.1,entry T.chains sc.1 sc.2))

theorem important_card : T.important.card ≤ Fintype.card V * Fintype.card I := by
  classical
  exact (Finset.card_image_le).trans (by simpa using Finset.card_le_univ T.active)

theorem entry_spec {s : V} {c : I} (h : (reachableIndices T.chains s c).Nonempty) :
    Reachable T.G s (entry T.chains s c) ∧
      label T.chains (entry T.chains s c) = some c := by
  classical
  have hm := Finset.min'_mem (reachableIndices T.chains s c) h
  simp only [entry,dite_eq_left h]
  exact ⟨(Finset.mem_filter.mp hm).2,label_node T.chains T.disjoint _ _⟩

theorem important_spec {s t : V} (hst : (s,t) ∈ T.important) :
    Reachable T.G s t ∧ first T.chains s t = t := by
  classical
  obtain ⟨⟨u,c⟩,huc,he⟩ := Finset.mem_image.mp hst
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  have hs := T.entry_spec (Finset.mem_filter.mp huc).2
  exact ⟨hs.1,by simp only [first,hs.2]⟩

/-- A one-edge insertion is allowed by the source-specific entry filter for
an important pair. Counting chains on a one-edge walk costs at most two. -/
theorem direct_repair (H : Finset (V × V)) {s t : V} (hst : (s,t) ∈ T.important) :
    T.distance (insert (s,t) H) s t ≤ 2 := by
  classical
  have hs := T.important_spec hst
  by_cases he : s = t
  · subst t
    exact (T.distance_le_walk _ hs.1 .nil (allowed_nil _ _)).trans
      ((T.count_le_vertices .nil).trans (by simp))
  · let p : DWalk s t := .cons (by simpa using he) .nil
    have hp : Allowed (T.graph (insert (s,t) H) s) p := by
      change Allowed (T.graph (insert (s,t) H) s) (Walk.cons _ Walk.nil)
      rw [allowed_cons]
      refine ⟨⟨Or.inr ?_,Or.inr (Or.inr hs.2)⟩,allowed_nil _ _⟩
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    exact (T.distance_le_walk _ hs.1 p hp).trans (by simpa [p] using T.count_le_vertices p)

noncomputable def potential (H : Finset (V × V)) : ℕ :=
  ∑ st ∈ T.important,T.distance H st.1 st.2

def stopped (D : ℕ) (H : Finset (V × V)) : Prop :=
  ∀ st ∈ T.important,T.distance H st.1 st.2 ≤ D

theorem stopped_mono (D : ℕ) : Monotone (T.stopped D) := by
  intro H J hHJ hH st hst
  exact (T.distance_antitone st.1 st.2 hHJ).trans (hH st hst)

theorem potential_antitone : Antitone T.potential := by
  intro H J hHJ
  exact Finset.sum_le_sum (fun st _ => T.distance_antitone st.1 st.2 hHJ)

theorem potential_le (H : Finset (V × V)) :
    T.potential H ≤ Fintype.card V * Fintype.card I ^ 2 := by
  classical
  calc
    T.potential H ≤ ∑ _st ∈ T.important,Fintype.card I :=
      Finset.sum_le_sum (fun st _ => T.distance_le_chains H st.1 st.2)
    _ = T.important.card * Fintype.card I := by simp
    _ ≤ (Fintype.card V * Fintype.card I) * Fintype.card I :=
      Nat.mul_le_mul_right _ T.important_card
    _ = Fintype.card V * Fintype.card I ^ 2 := by ring

/-- Strict progress is proved for this graph model; only the much stronger
cubic rate from Lemma 5.7 remains an open obligation. -/
theorem progress (D : ℕ) (hD : 2 ≤ D) (H : Finset (V × V))
    (hbad : ¬ T.stopped D H) :
    ∃ e ∈ candidates T.G,T.potential (insert e H) < T.potential H := by
  classical
  simp only [stopped, not_forall, not_le] at hbad
  obtain ⟨⟨s,t⟩,hst,hfar⟩ := hbad
  dsimp only at hfar
  have hs := T.important_spec hst
  have hne : s ≠ t := by
    intro he
    subst t
    have hh := (T.distance_le_walk H hs.1 .nil (allowed_nil _ _)).trans (T.count_le_vertices .nil)
    simp only [Walk.length_nil] at hh
    omega
  refine ⟨(s,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,hs.1⟩
  · apply Finset.sum_lt_sum
    · intro st hst'
      exact T.distance_antitone st.1 st.2 (Finset.subset_insert _ _)
    · exact ⟨(s,t),hst,(T.direct_repair H hst).trans_lt (hD.trans_lt hfar)⟩

end GreedyShortcuts.ChainDistance.Context
