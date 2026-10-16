import SlackSparsification.ReachabilityHalfCover

/-! Constructive minimal-preserver and required-edge foundations.
No sourcewise cardinality bound is assumed or proved in this module. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def PreservesReachability (K : SimpleGraph V) (A : V → V → Prop)
    (P F : Finset (V × V)) : Prop :=
  ∀ st ∈ P, Reachable K A st.1 st.2 → Reachable K (edgeRel F) st.1 st.2

/-- Nonvacuous requirement: the pair is reachable, and every allowed walk uses e. -/
def Requires (K : SimpleGraph V) (F : Finset (V × V)) (s t : V) (e : V × V) : Prop :=
  Reachable K (edgeRel F) s t ∧ ∀ p : K.Walk s t, Allowed (edgeRel F) p → e ∈ arcs p

omit [DecidableEq V] in
/-- Finite minimum-cardinality preserver on actual input arcs, for any orientation. -/
theorem exists_minimal_reachability (K : SimpleGraph V) (A : V → V → Prop)
    (P : Finset (V × V)) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧ PreservesReachability K A P F ∧
      ∀ J : Finset (V × V), J ⊆ inputArcs K A → PreservesReachability K A P J → F.card ≤ J.card := by
  classical
  have hfull : PreservesReachability K A P (inputArcs K A) := by
    intro st _ hr
    obtain ⟨p,hp⟩ := hr
    exact ⟨p,fun d hd => mem_filter.mpr ⟨mem_univ _,d.adj,hp d hd⟩⟩
  let Good := fun n => ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
    PreservesReachability K A P F ∧ F.card = n
  have hex : ∃ n, Good n := ⟨_,inputArcs K A,Subset.rfl,hfull,rfl⟩
  obtain ⟨F,hF,hp,hc⟩ := Nat.find_spec hex
  refine ⟨F,hF,hp,?_⟩
  intro J hJ hsat
  rw [hc]
  exact Nat.find_min' hex ⟨J,hJ,hsat,rfl⟩

/-- Every arc of a minimal preserver has a reachable demand witnessing necessity. -/
theorem minimal_arc_required {K : SimpleGraph V} {A : V → V → Prop}
    {P F : Finset (V × V)} (hF : F ⊆ inputArcs K A) (hs : PreservesReachability K A P F)
    (hmin : ∀ J : Finset (V × V), J ⊆ inputArcs K A → PreservesReachability K A P J → F.card ≤ J.card)
    {e : V × V} (he : e ∈ F) :
    ∃ st ∈ P, Reachable K A st.1 st.2 ∧ Requires K F st.1 st.2 e := by
  classical
  have hn : ¬ PreservesReachability K A P (F.erase e) := by
    intro h
    have hc := hmin (F.erase e) ((erase_subset e F).trans hF) h
    exact (Nat.not_le_of_lt (card_erase_lt_of_mem he)) hc
  simp only [PreservesReachability, not_forall] at hn
  obtain ⟨st,hst⟩ := hn
  obtain ⟨hst,hr,hfail⟩ := hst
  refine ⟨st,hst,hr,hs st hst hr,?_⟩
  intro p hp
  by_contra hnot
  apply hfail
  refine ⟨p,allowed_of_arcs p ?_⟩
  intro a ha
  exact mem_erase.mpr ⟨by intro h; change a = e at h; exact hnot (h ▸ ha),arcs_allowed p hp ha⟩

omit [DecidableEq V] in
/-- Empty or wholly unreachable demand sets have the empty minimal witness. -/
theorem minimal_empty_of_no_reachable {K : SimpleGraph V} {A : V → V → Prop}
    {P F : Finset (V × V)}
    (hmin : ∀ J : Finset (V × V), J ⊆ inputArcs K A → PreservesReachability K A P J → F.card ≤ J.card)
    (hn : ∀ st ∈ P, ¬ Reachable K A st.1 st.2) : F = ∅ := by
  apply card_eq_zero.mp
  have h := hmin ∅ (empty_subset _) (fun st hst hr => (hn st hst hr).elim)
  simpa using h

omit [Fintype V] in
theorem path_incoming_unique {K : SimpleGraph V} {s t : V} (p : K.Walk s t)
    (hp : p.IsPath) {e f : V × V} (he : e ∈ arcs p) (hf : f ∈ arcs p)
    (hh : e.2 = f.2) : e = f := by
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
  have hn : (p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.support_nodup.tail
  have h := List.inj_on_of_nodup_map hn hd ha hh
  exact congrArg (fun d : K.Dart => (d.fst,d.snd)) h

omit [Fintype V] in
theorem path_no_incoming_start {K : SimpleGraph V} {s t : V} (p : K.Walk s t)
    (hp : p.IsPath) {e : V × V} (he : e ∈ arcs p) : e.2 ≠ s := by
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  have hn : (s :: p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.cons_map_snd_darts]
    exact hp.support_nodup
  intro h
  have hm : d.snd ∈ p.darts.map (fun d => d.snd) := List.mem_map.mpr ⟨d,hd,rfl⟩
  rw [h] at hm
  exact (List.nodup_cons.mp hn).1 hm

/-- Required edges entering one vertex for a fixed demand must coincide. -/
theorem required_same_demand_same_vertex {K : SimpleGraph V} {F : Finset (V × V)}
    {s t : V} {e f : V × V} (he : Requires K F s t e) (hf : Requires K F s t f)
    (hh : e.2 = f.2) : e = f := by
  obtain ⟨p,hp⟩ := exists_optimal (edgeRel F) (fun _ _ => 0) s t he.1
  exact path_incoming_unique p hp.2.1 (he.2 p hp.1) (hf.2 p hp.1) hh

/-- Same-source requirements entering the same vertex coincide, even with
separate targets. This supplies the same-vertex case of collision uniqueness. -/
theorem required_same_source_same_vertex {K : SimpleGraph V} {F : Finset (V × V)}
    {s t u : V} {e f : V × V} (he : Requires K F s t e) (hf : Requires K F s u f)
    (hh : e.2 = f.2) : e = f := by
  obtain ⟨p,hp⟩ := exists_optimal (edgeRel F) (fun _ _ => 0) s t he.1
  obtain ⟨q,hq⟩ := exists_optimal (edgeRel F) (fun _ _ => 0) s u hf.1
  have hep := he.2 p hp.1
  have hfq := hf.2 q hq.1
  have hmem : ∀ {a b : V} (w : K.Walk a b) (x : V × V), x ∈ arcs w → x.2 ∈ w.support := by
    intro a b w x hx
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    have hm : d.snd ∈ w.darts.map (fun d => d.snd) := List.mem_map.mpr ⟨d,hd,rfl⟩
    rw [Walk.map_snd_darts] at hm
    exact List.mem_of_mem_tail hm
  have hvp : f.2 ∈ p.support := hh ▸ hmem p e hep
  have hvq := hmem q f hfq
  let left := p.takeUntil f.2 hvp
  let right := q.dropUntil f.2 hvq
  have hal : Allowed (edgeRel F) left := fun d hd => hp.1 d (p.darts_takeUntil_subset_darts hvp hd)
  have har : Allowed (edgeRel F) right := fun d hd => hq.1 d (q.darts_dropUntil_subset_darts hvq hd)
  have hfr := hf.2 (left.append right) ((allowed_append _ _ _).mpr ⟨hal,har⟩)
  have hfleft : f ∈ arcs left := by
    have hsplit : f ∈ arcs left ∨ f ∈ arcs right := by
      simpa [arcs,arcList,Walk.darts_append,List.map_append] using hfr
    rcases hsplit with h | h
    · exact h
    · have hpath : right.IsPath := Walk.isPath_of_isSubwalk (q.isSubwalk_dropUntil hvq) hq.2.1
      exact (path_no_incoming_start right hpath h rfl).elim
  have hfp : f ∈ arcs p := by
    obtain ⟨d,hd,hdf⟩ := List.mem_map.mp (List.mem_toFinset.mp hfleft)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨d,p.darts_takeUntil_subset_darts hvp hd,hdf⟩)
  exact path_incoming_unique p hp.2.1 hep hfp hh


/-- The same-vertex collision case yields equality of both incoming edges,
not merely equality of the vertices. No DAG assumption is needed here. -/
theorem collision_same_vertex {K : SimpleGraph V} {F : Finset (V × V)}
    {a b s t u : V} {e e' f f' : V × V}
    (he : Requires K F a b e) (he' : Requires K F a b e')
    (hf : Requires K F s t f) (hf' : Requires K F s u f')
    (h1 : e.2 = f.2) (h2 : e'.2 = f'.2) (hv : e.2 = e'.2) :
    e = e' ∧ f = f' := by
  exact ⟨required_same_demand_same_vertex he he' hv,
    required_same_source_same_vertex hf hf' (h1.symm.trans (hv.trans h2))⟩

omit [DecidableEq V] in
/-- A source-constrained demand set with zero sources is empty. -/
theorem zero_sources_empty_demands (R : Finset V) (P : Finset (V × V))
    (hR : R.card = 0) (hP : ∀ st ∈ P, st.1 ∈ R) : P = ∅ := by
  have hr : R = ∅ := card_eq_zero.mp hR
  apply eq_empty_iff_forall_notMem.mpr
  intro st hst
  simpa [hr] using hP st hst

/-- Light arcs are bounded without any requirement or acyclicity premise.
The subsequent heavy-edge argument will use a positive cutoff d. -/
theorem light_arcs_card (F : Finset (V × V)) (d : ℕ) :
    (F.filter fun e => (F.filter fun a => a.2 = e.2).card ≤ d).card ≤ Fintype.card V * d := by
  classical
  let L := F.filter fun e => (F.filter fun a => a.2 = e.2).card ≤ d
  let I := fun v => if (F.filter fun a => a.2 = v).card ≤ d then
    F.filter (fun a => a.2 = v) else ∅
  have hsub : L ⊆ (univ : Finset V).biUnion I := by
    intro e he
    obtain ⟨he,hc⟩ := mem_filter.mp he
    apply mem_biUnion.mpr
    refine ⟨e.2,mem_univ _,?_⟩
    simp only [I,if_pos hc]
    exact mem_filter.mpr ⟨he,rfl⟩
  have hI : ∀ v, (I v).card ≤ d := by
    intro v
    dsimp [I]
    split_ifs with h
    · exact h
    · simp
  calc
    L.card ≤ ((univ : Finset V).biUnion I).card := card_le_card hsub
    _ ≤ ∑ v ∈ (univ : Finset V), (I v).card := card_biUnion_le
    _ ≤ ∑ _ ∈ (univ : Finset V), d := sum_le_sum (fun v _ => hI v)
    _ = Fintype.card V * d := by simp

end SlackSparsification.Directed
