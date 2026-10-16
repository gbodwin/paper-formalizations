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
  simp only [not_imp] at hst
  obtain ⟨hst,hr,hfail⟩ := hst
  refine ⟨st,hst,hr,hs st hst hr,?_⟩
  intro p hp
  by_contra hnot
  apply hfail
  refine ⟨p,allowed_of_arcs p ?_⟩
  intro a ha
  exact mem_erase.mpr ⟨by intro h; subst a; exact hnot ha,arcs_allowed p hp ha⟩

/-- Empty or wholly unreachable demand sets have the empty minimal witness. -/
theorem minimal_empty_of_no_reachable {K : SimpleGraph V} {A : V → V → Prop}
    {P F : Finset (V × V)}
    (hmin : ∀ J : Finset (V × V), J ⊆ inputArcs K A → PreservesReachability K A P J → F.card ≤ J.card)
    (hn : ∀ st ∈ P, ¬ Reachable K A st.1 st.2) : F = ∅ := by
  apply card_eq_zero.mp
  have h := hmin ∅ (empty_subset _) (fun st hst hr => (hn st hst hr).elim)
  simpa using h

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] in
theorem path_no_incoming_start {K : SimpleGraph V} {s t : V} (p : K.Walk s t)
    (hp : p.IsPath) {e : V × V} (he : e ∈ arcs p) : e.2 ≠ s := by
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  have hn : (s :: p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.cons_map_snd_darts]
    exact hp.support_nodup
  intro h
  exact (List.nodup_cons.mp hn).1 (h ▸ List.mem_map.mpr ⟨d,hd,rfl⟩)

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

end SlackSparsification.Directed
