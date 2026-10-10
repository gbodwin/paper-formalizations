import GreedyShortcuts.ChainSuffixCharging

/-! Attained chain-count levels on an actual valid walk. Integer levels are
reached at real earliest-entry vertices, with the original source retained. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem chainSet_copy {s t u v : V} (p : DWalk s t) (hs : s=u) (ht : t=v) :
    T.chainSet (p.copy hs ht)=T.chainSet p := by
  simp only [chainSet,Walk.support_copy]

theorem chainSet_take_one {s t : V} (p : DWalk s t) :
    T.chainSet (p.take 1) = (label T.chains s).toFinset ∪
      (label T.chains (p.getVert 1)).toFinset := by
  classical
  cases p <;> simp [Walk.take,chainSet]

theorem label_subset_chainSet_end {s t : V} (p : DWalk s t) :
    (label T.chains t).toFinset ⊆ T.chainSet p := by
  intro c hc
  exact (T.mem_chainSet p c).mpr ⟨t,p.end_mem_support,by simpa using hc⟩

theorem chainSet_take_succ {s t : V} (p : DWalk s t) (i : ℕ) :
    T.chainSet (p.take (i+1)) = T.chainSet (p.take i) ∪
      (label T.chains (p.getVert (i+1))).toFinset := by
  classical
  rw [Walk.take_add_eq,T.chainSet_copy,T.chainSet_append,T.chainSet_take_one,
    ← Finset.union_assoc,Finset.union_eq_left.mpr (T.label_subset_chainSet_end (p.take i))]
  simp only [Walk.drop_getVert]

theorem count_take_succ_le {s t : V} (p : DWalk s t) (i : ℕ) :
    T.count (p.take (i+1)) ≤ T.count (p.take i)+1 := by
  classical
  have hc : (label T.chains (p.getVert (i+1))).toFinset.card ≤ 1 := by
    cases label T.chains (p.getVert (i+1)) <;> simp
  unfold count
  rw [T.chainSet_take_succ]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hc _)

/-- Every positive count above the initial singleton contribution is reached
exactly, rather than skipped by a multi-chain jump. -/
theorem exists_prefix_count {s t : V} (p : DWalk s t) (k : ℕ)
    (hk : 2 ≤ k) (hkp : k ≤ T.count p) :
    ∃ i, 0 < i ∧ i ≤ p.length ∧ T.count (p.take i) = k ∧ T.count (p.take (i-1)) < k := by
  classical
  have hend : T.count (p.take p.length)=T.count p := by
    unfold count
    rw [Walk.take_of_length_le (Nat.le_refl _),T.chainSet_copy]
  have hex : ∃ i,k ≤ T.count (p.take i) := ⟨p.length,by rw [hend];exact hkp⟩
  let i := Nat.find hex
  have hi : k ≤ T.count (p.take i) := Nat.find_spec hex
  have hil : i ≤ p.length := Nat.find_min' hex (by rw [hend];exact hkp)
  have hi0 : 0 < i := by
    by_contra hn
    have he : i=0 := by omega
    have hc := T.count_le_vertices (p.take 0)
    simp only [Walk.take_length,Nat.zero_min] at hc
    rw [he] at hi
    omega
  have hprev : T.count (p.take (i-1)) < k := by
    exact Nat.lt_of_not_ge (Nat.find_min hex (by omega : i-1 < i))
  have hstep := T.count_take_succ_le p (i-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at hstep
  exact ⟨i,hi0,hil,by omega,hprev⟩

omit [Fintype V] [DecidableEq V] in
theorem allowed_vertex_step {F : V → V → Prop} {s t : V}
    (p : DWalk s t) (hp : Allowed F p) (i : ℕ) (hi : i < p.length) :
    F (p.getVert i) (p.getVert (i+1)) := by
  have hd : i < p.darts.length := by simpa only [Walk.length_darts] using hi
  have h := hp (p.darts[i]'hd) (List.getElem_mem hd)
  simpa only [Walk.darts_getElem_eq_getVert] using h

/-- The first attainment of a new count level is an actual important entry,
not an arbitrary covered or uncovered vertex. -/
theorem prefix_level_important {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (i : ℕ) (hi : i < p.length)
    (hinc : T.count (p.take i) < T.count (p.take (i+1))) :
    (s,p.getVert (i+1)) ∈ T.important := by
  classical
  have hset := T.chainSet_take_succ p i
  have hlabel : label T.chains (p.getVert (i+1)) ≠ none := by
    intro hn
    simp only [hn,Option.toFinset_none,Finset.union_empty] at hset
    have he : T.count (p.take (i+1))=T.count (p.take i) := congrArg Finset.card hset
    omega
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hlabel
  have hcnot : c ∉ T.chainSet (p.take i) := by
    intro hm
    simp only [hc,Option.toFinset_some,Finset.union_singleton,Finset.insert_eq_of_mem hm] at hset
    have he : T.count (p.take (i+1))=T.count (p.take i) := congrArg Finset.card hset
    omega
  have hprev : label T.chains (p.getVert i) ≠ label T.chains (p.getVert (i+1)) := by
    intro he
    exact hcnot ((T.mem_chainSet (p.take i) c).mpr
      ⟨p.getVert i,(p.take i).end_mem_support,he.trans hc⟩)
  have hedge := allowed_vertex_step p hp i hi
  have hf := hedge.2.resolve_left hprev |>.resolve_left hlabel
  have hr : Reachable T.G s (p.getVert (i+1)) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.take (i+1),allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hp (p.isSubwalk_take (i+1)))⟩
  simpa only [hf] using T.first_important hr hc

/-- Any chosen noninitial chain level is realized by a legal important
prefix endpoint in the same native path. -/
theorem exists_important_prefix_count {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (k : ℕ) (hk : 2 ≤ k) (hkp : k ≤ T.count p) :
    ∃ i,i ≤ p.length ∧ T.count (p.take i)=k ∧ (s,p.getVert i) ∈ T.important := by
  obtain ⟨i,hi,hil,hcount,hprev⟩ := T.exists_prefix_count p k hk hkp
  refine ⟨i,hil,hcount,?_⟩
  have he : i-1+1=i := Nat.sub_add_cancel (by omega)
  have hpair := T.prefix_level_important hH p hp (i-1) (by omega) (by rw [he];omega)
  simpa only [he] using hpair

end GreedyShortcuts.ChainDistance.Context
