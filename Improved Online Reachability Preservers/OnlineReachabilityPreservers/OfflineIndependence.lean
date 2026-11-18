import OnlineReachabilityPreservers.PairwiseInitial

/-! Greedy pruning and the constructive independence reduction on DAGs. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [LinearOrder V] [Fintype V]

private def serves (G H : Arcs V) (D : List (V × V)) : Bool :=
  D.all fun d => !decide (d.1 ∈ reaches G d.2) || decide (d.1 ∈ reaches H d.2)

private theorem serves_spec (G H : Arcs V) (D : List (V × V)) :
    serves G H D = true ↔ ∀ d ∈ D, Reach G d.1 d.2 → Reach H d.1 d.2 := by
  simp only [serves, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, mem_reaches]
  classical
  simp [or_iff_not_imp_left]

private def removeIfSafe (G : Arcs V) (D : List (V × V)) (H : Arcs V) (e : V × V) : Arcs V :=
  if serves G (H.erase e) D then H.erase e else H

private theorem removeIfSafe_subset (G H : Arcs V) (D : List (V × V)) (e : V × V) :
    removeIfSafe G D H e ⊆ H := by
  unfold removeIfSafe
  split
  · exact erase_subset _ _
  · exact subset_rfl

private theorem removeIfSafe_serves (G H : Arcs V) (D : List (V × V)) (e : V × V)
    (hh : serves G H D = true) :
    serves G (removeIfSafe G D H e) D = true := by
  unfold removeIfSafe
  split <;> assumption

private def prune (G : Arcs V) (D : List (V × V)) (H : Arcs V) (edges : List (V × V)) : Arcs V :=
  edges.foldl (removeIfSafe G D) H

private theorem prune_subset (G H : Arcs V) (D L : List (V × V)) :
    prune G D H L ⊆ H := by
  induction L generalizing H with
  | nil => exact subset_rfl
  | cons e es ih => exact (ih _).trans (removeIfSafe_subset G H D e)

private theorem prune_serves (G H : Arcs V) (D L : List (V × V)) (hh : serves G H D = true) :
    serves G (prune G D H L) D = true := by
  induction L generalizing H with
  | nil => exact hh
  | cons e es ih => exact ih _ (removeIfSafe_serves G H D e hh)

private theorem prune_critical (G H : Arcs V) (D L : List (V × V)) {e : V × V}
    (hL : e ∈ L) (he : e ∈ prune G D H L) :
    ∃ d ∈ D, Reach G d.1 d.2 ∧ ¬ Reach ((prune G D H L).erase e) d.1 d.2 := by
  induction L generalizing H with
  | nil => simp at hL
  | cons a as ih =>
    let H' := removeIfSafe G D H a
    change e ∈ prune G D H' as at he
    change ∃ d ∈ D, Reach G d.1 d.2 ∧ ¬ Reach ((prune G D H' as).erase e) d.1 d.2
    rcases List.mem_cons.mp hL with rfl | hmem
    · have eh := prune_subset G H' D as he
      have hw : ¬ serves G (H.erase e) D = true := by
        intro test
        simp [H', removeIfSafe, test] at eh
      have hbad := (not_congr (serves_spec G (H.erase e) D)).mp hw
      simp only [not_forall] at hbad
      obtain ⟨d, hd, hr, hno⟩ := hbad
      refine ⟨d, hd, hr, fun h => hno (reach_mono ?_ h)⟩
      apply erase_subset_erase
      exact (prune_subset G H' D as).trans (removeIfSafe_subset G H D _)
    · exact ih H' hmem he

/-- Inspect each input edge once in lexicographic order, deleting it when all demands stay served. -/
def offlinePrune (G : Arcs V) (D : List (V × V)) : Arcs V :=
  prune G D G ((G.image toLex).sort (· ≤ ·) |>.map ofLex)

theorem offlinePrune_spec (G : Arcs V) (D : List (V × V)) :
    offlinePrune G D ⊆ G ∧ Preserves G (offlinePrune G D) D := by
  have sub : offlinePrune G D ⊆ G := prune_subset _ _ _ _
  have good : serves G (offlinePrune G D) D = true :=
    prune_serves G G D _ ((serves_spec G G D).mpr (fun _ _ h => h))
  exact ⟨sub, fun d hd => ⟨reach_mono sub, (serves_spec G _ D).mp good d hd⟩⟩

/-- Every retained edge is essential to at least one reachable original demand. -/
theorem offlinePrune_critical (G : Arcs V) (D : List (V × V)) {e : V × V}
    (he : e ∈ offlinePrune G D) :
    ∃ d ∈ D, Reach G d.1 d.2 ∧ ¬ Reach ((offlinePrune G D).erase e) d.1 d.2 := by
  have heG := (offlinePrune_spec G D).1 he
  apply prune_critical G G D _ ?_ he
  exact List.mem_map.mpr ⟨toLex e, (mem_sort _).mpr (mem_image_of_mem _ heG), rfl⟩

private def criticalOwner (H : Arcs V) (D : List (V × V)) (e : V × V) : Option (Fin D.length) :=
  least? (univ.filter fun i : Fin D.length =>
    (D.get i).1 ∈ reaches H (D.get i).2 ∧ (D.get i).1 ∉ reaches (H.erase e) (D.get i).2)

private def owned (H : Arcs V) (D : List (V × V)) (i : Fin D.length) : Arcs V :=
  H.filter fun e => criticalOwner H D e = some i

private theorem owned_critical {H : Arcs V} {D : List (V × V)} {i : Fin D.length} {e : V × V}
    (he : e ∈ owned H D i) :
    Reach H (D.get i).1 (D.get i).2 ∧ ¬ Reach (H.erase e) (D.get i).1 (D.get i).2 := by
  have owner := (mem_filter.mp he).2
  obtain ⟨hh, hno⟩ := (mem_filter.mp (least?_mem owner)).2
  exact ⟨mem_reaches.mp hh, fun h => hno (mem_reaches.mpr h)⟩

private theorem owned_has_path {H : Arcs V} (dag : IsDAG H) {D : List (V × V)}
    {i : Fin D.length} {e : V × V} (he : e ∈ owned H D i) :
    e ∈ forwardEdges H ∅ (D.get i) := by
  obtain ⟨hr, hno⟩ := owned_critical he
  obtain ⟨p, hp⟩ := (forwardPath_succeeds (empty_subset _) dag).mpr hr
  have w := (forwardPath_spec (empty_subset _) hp).1
  have hem : e ∈ p := by
    by_contra h
    apply hno
    refine reach_mono ?_ w.in_edges.reachable
    intro f hf
    have hpf := List.mem_toFinset.mp hf
    exact mem_erase.mpr ⟨fun eq => h (eq ▸ hpf), w.mem hpf⟩
  change e ∈ ((forwardPath H ∅ (D.get i).1 (D.get i).2).getD []).toFinset
  rw [hp]
  exact List.mem_toFinset.mpr hem

private theorem sum_owned {H : Arcs V} {D : List (V × V)}
    (critical : ∀ e ∈ H, ∃ d ∈ D, Reach H d.1 d.2 ∧ ¬ Reach (H.erase e) d.1 d.2) :
    (∑ i, (owned H D i).card) = H.card := by
  have total : (univ : Finset (Fin D.length)).biUnion (owned H D) = H := by
    ext e
    constructor
    · intro h
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
      exact (mem_filter.mp hi).1
    · intro he
      obtain ⟨d, hd, hr, hno⟩ := critical e he
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
      have hk : i ∈ univ.filter (fun i : Fin D.length => (D.get i).1 ∈ reaches H (D.get i).2 ∧
          (D.get i).1 ∉ reaches (H.erase e) (D.get i).2) :=
        mem_filter.mpr ⟨mem_univ _, mem_reaches.mpr hr, fun hm => hno (mem_reaches.mp hm)⟩
      obtain ⟨j, hj⟩ := least?_some ⟨i, hk⟩
      exact mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨he, hj⟩⟩
  have disj : ((univ : Finset (Fin D.length)) : Set (Fin D.length)).PairwiseDisjoint (owned H D) := by
    intro i _ j _ hne
    apply disjoint_left.mpr
    intro e he hf
    exact hne (Option.some.inj ((mem_filter.mp he).2.symm.trans (mem_filter.mp hf).2))
  calc
    _ = ((univ : Finset (Fin D.length)).biUnion (owned H D)).card := (card_biUnion disj).symm
    _ = _ := congrArg Finset.card total

/-- Critical-edge tails and the destination of each request in the offline preserver. -/
def criticalCompressed (H : Arcs V) (D : List (V × V)) (i : Fin D.length) : Finset V :=
  markedPath (owned H D i) (D.get i).2

def CriticalBefore (H : Arcs V) (D : List (V × V)) (i : Fin D.length) (x y : V) : Prop :=
  BeforeIn H (criticalCompressed H D i) x y

private theorem critical_to_target {H : Arcs V} (dag : IsDAG H) {D : List (V × V)} {i : Fin D.length}
    {x : V} (hx : x ∈ criticalCompressed H D i) : Reach H x (D.get i).2 :=
  markedPath_to_target (empty_subset _) (fun _ he => owned_has_path dag he) hx

private theorem critical_exit {H : Arcs V} (dag : IsDAG H) {D : List (V × V)} {i : Fin D.length}
    {x y : V} (h : CriticalBefore H D i x y) :
    ∃ e ∈ owned H D i, e.1 = x ∧ Reach H e.2 y :=
  markedPath_exit dag (empty_subset _) (fun _ he => owned_has_path dag he) h

private theorem edge_from_source {H : Arcs V} {D : List (V × V)} {i : Fin D.length}
    (dag : IsDAG H) {e : V × V} (he : e ∈ owned H D i) : Reach H (D.get i).1 e.1 := by
  obtain ⟨p, hp⟩ := (forwardPath_succeeds (empty_subset _) dag).mpr (owned_critical he).1
  have hem := owned_has_path dag he
  change e ∈ ((forwardPath H ∅ (D.get i).1 (D.get i).2).getD []).toFinset at hem
  rw [hp] at hem
  exact (forwardPath_spec (empty_subset _) hp).1.from_start (List.mem_toFinset.mp hem)

omit [Fintype V] in
private theorem reach_erase_of_no_tail {H : Arcs V} {e : V × V} {s t : V}
    (walk : Reach H s t) (hno : ¬ Reach H s e.1) : Reach (H.erase e) s t := by
  induction walk with
  | refl => exact .refl
  | @tail u v pre edge ih =>
    refine ih.tail (mem_erase.mpr ⟨?_, edge⟩)
    intro eq
    exact hno ((congrArg Prod.fst eq) ▸ pre)

omit [Fintype V] in
private theorem reach_erase_of_no_suffix {H : Arcs V} {e : V × V} {s t : V}
    (walk : Reach H s t) (hno : ¬ Reach H e.2 t) : Reach (H.erase e) s t := by
  induction walk with
  | refl => exact .refl
  | @tail u v pre edge ih =>
    refine (ih (fun h => hno (h.tail edge))).tail (mem_erase.mpr ⟨?_, edge⟩)
    intro eq
    exact hno ((congrArg Prod.snd eq).symm ▸ ReflTransGen.refl)

theorem criticalCompressed_bridge_free {H : Arcs V} (dag : IsDAG H) (D : List (V × V))
    (k : ℕ) : IsEmpty (Bridge (CriticalBefore H D) k) := by
  refine ⟨fun b => ?_⟩
  obtain ⟨e, he, hex, _⟩ := critical_exit dag b.riverStep
  obtain ⟨f, hf, hfx, hnext⟩ := critical_exit dag (b.arcStep 0)
  have htail : f.1 = e.1 := hfx.trans hex.symm
  have hne : f ≠ e := by
    intro eq
    subst f
    exact b.river_ne_arc 0 (Option.some.inj ((mem_filter.mp he).2.symm.trans (mem_filter.mp hf).2))
  have chain (j : Fin (k + 1)) : Reach H (b.vertex (0 : Fin (k + 1)).succ)
      (b.vertex j.succ) := by
    induction j using Fin.induction with
    | zero => exact .refl
    | succ j ih => exact ih.trans (b.arcStep j.succ).2.2.2
  have concat : Reach H f.2 (D.get b.river).2 :=
    (hnext.trans (chain (Fin.last k))).trans (critical_to_target dag b.riverStep.2.1)
  have start : Reach (H.erase e) (D.get b.river).1 e.1 :=
    reach_erase_of_no_suffix (edge_from_source dag he) (dag (mem_filter.mp he).1)
  have finish : Reach (H.erase e) f.2 (D.get b.river).2 :=
    reach_erase_of_no_tail concat (fun h => dag (mem_filter.mp hf).1 (htail.symm ▸ h))
  have first : Edge (H.erase e) e.1 f.2 := htail ▸ mem_erase.mpr ⟨hne, (mem_filter.mp hf).1⟩
  exact (owned_critical he).2 (start.trans (finish.head first))

theorem criticalCompressed_card {H : Arcs V} (dag : IsDAG H) (D : List (V × V))
    (critical : ∀ e ∈ H, ∃ d ∈ D, Reach H d.1 d.2 ∧ ¬ Reach (H.erase e) d.1 d.2) :
    (∑ i : Fin D.length, (criticalCompressed H D i).card) = H.card + D.length := by
  have point (i : Fin D.length) : (criticalCompressed H D i).card = (owned H D i).card + 1 :=
    markedPath_card dag (empty_subset _) (fun _ he => owned_has_path dag he)
  simp only [point, sum_add_distrib, sum_owned critical, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

/-- Constructive independence on DAGs. Prune dispensable edges, then assign each retained
edge to a request that needs it. The compressed family is acyclic and has no bridges. -/
theorem theorem14_dag_compression {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    let H := offlinePrune G D
    let paths := topologicalPaths H (criticalCompressed H D)
    H ⊆ G ∧ Preserves G H D ∧
      (∑ i : Fin D.length, (paths i).card) = H.card + D.length ∧
      ∀ size, BridgeFree (PathBefore paths) size := by
  let H := offlinePrune G D
  obtain ⟨sub, correct⟩ := offlinePrune_spec G D
  have hd : IsDAG H := fun _ _ he h => dag (sub he) (reach_mono sub h)
  have count := criticalCompressed_card hd D ?_
  · refine ⟨sub, correct, by simpa only [topologicalPaths, card_map] using count, ?_⟩
    intro size k _
    refine ⟨fun b => ?_⟩
    let former : Bridge (CriticalBefore H D) k :=
      b.reverse.mapVertices (topologicalEquiv H).symm (topologicalEquiv H).symm.injective
        (fun _ _ _ h => topologicalPaths_step hd
          (fun i {_ _} hx hy ne => markedPath_total (empty_subset _)
            (fun _ he => owned_has_path (D := D) (i := i) hd he) hx hy ne)
          h)
    exact (criticalCompressed_bridge_free hd D k).false former
  · intro e he
    obtain ⟨d, hm, hr, hno⟩ := offlinePrune_critical G D he
    exact ⟨d, hm, (correct d hm).mpr hr, hno⟩

theorem offlinePrune_pairwise_initial {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    let m := (offlinePrune G D).card
    let n := Fintype.card V
    m ≤ 16*n ∨ m^3 ≤ 2048 * (n*D.length)^2 := by
  let H := offlinePrune G D
  let paths := topologicalPaths H (criticalCompressed H D)
  let : Fintype (Set.range (reverseTopologicalKey H)) := Fintype.ofEquiv V (topologicalEquiv H)
  obtain ⟨_, _, count, free⟩ := theorem14_dag_compression dag D
  have bound := lemma27_acyclic paths (free 4).halfFree
  change (∑ i : Fin D.length, (paths i).card) = H.card + D.length at count
  simp only [← Fintype.card_congr (topologicalEquiv H), Fintype.card_fin, count] at bound
  have cap := card_le_univ H
  rw [Fintype.card_prod, ← pow_two] at cap
  exact edge_bound_of_incidence cap bound

/-- Offline pruning after SCC contraction, with fixed connector edges lifted to the input. -/
def offlinePreserver (G : Arcs V) (D : List (V × V)) : Arcs V := liftedRun offlinePrune G D

theorem offline_pairwise_initial (G : Arcs V) (D : List (V × V)) :
    let H := offlinePreserver G D
    let n := Fintype.card V
    H ⊆ G ∧ Preserves G H D ∧
      (H.card ≤ 18*n ∨ (H.card - 2*n)^3 ≤ 2048*(n*D.length)^2) := by
  obtain ⟨sub, correct, overhead⟩ := theorem9_lift offlinePrune G D
    (fun K _ P => (offlinePrune_spec K P).1) (fun K _ P => (offlinePrune_spec K P).2)
  have bound := offlinePrune_pairwise_initial (condensation_dag G) (D.map (projectDemand G))
  simp only [List.length_map] at bound
  refine ⟨sub, correct, ?_⟩
  change (offlinePreserver G D).card ≤ _ at overhead
  rcases bound with bound | bound
  · exact Or.inl (by omega)
  · exact Or.inr ((Nat.pow_le_pow_left (show (offlinePreserver G D).card - 2 * Fintype.card V ≤
        (offlinePrune (condensation G) (D.map (projectDemand G))).card by omega) 3).trans bound)

end OnlineReachabilityPreservers
