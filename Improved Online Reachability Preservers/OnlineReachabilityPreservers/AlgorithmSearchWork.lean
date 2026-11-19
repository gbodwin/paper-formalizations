import OnlineReachabilityPreservers.OfflineIndependence
import OnlineReachabilityPreservers.RouteWork

/-! Compose the search counts through the deterministic digraph algorithms. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Arc inspections for SCC labels during projection, representative
selection and connector construction, including the hop searches. -/
def liftSearchWorkBound (n m p : ℕ) : ℕ :=
  (4*m+2*p+2*m^2+2*n)*(2*n*m) + 2*n*((n+1)*n*m+n*m)

/-- Run the search counter for a condensed algorithm once.
The outer count charges each SCC label and connector search. -/
def liftedRunWithSearchWork (run : Arcs V → List (V × V) → Arcs V × ℕ)
    (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ :=
  match D with
  | [] => (∅, 0)
  | _ :: _ =>
    let cross := G.filter (fun e => componentLabel G e.1 ≠ componentLabel G e.2)
    let core := run (cross.image (projectDemand G)) (D.map (projectDemand G))
    let n := Fintype.card V
    let m := G.card
    let labels := 2*m+2*cross.card+2*D.length+2*m*core.1.card+2*n
    (connectors G ∪ liftedArcs G core.1,
      labels*(2*n*m)+2*n*((n+1)*n*m+n*m)+core.2)

theorem liftedRunWithSearchWork_spec
    (metered : Arcs V → List (V × V) → Arcs V × ℕ)
    (run : Arcs V → List (V × V) → Arcs V)
    (same : ∀ K T, (metered K T).1 = run K T)
    (sub : ∀ K T, run K T ⊆ K)
    (G : Arcs V) (D : List (V × V)) :
    let result := liftedRunWithSearchWork metered G D
    result.1 = liftedRun run G D ∧ result.2 ≤
      liftSearchWorkBound (Fintype.card V) G.card D.length +
        (metered (condensation G) (D.map (projectDemand G))).2 := by
  cases D with
  | nil => simp [liftedRunWithSearchWork, liftedRun]
  | cons d rest =>
    let D := d :: rest
    let K := condensation G
    let H := metered K (D.map (projectDemand G))
    let cross := G.filter (fun e => componentLabel G e.1 ≠ componentLabel G e.2)
    have sameH : H.1 = run K (D.map (projectDemand G)) := same _ _
    have raw := (liftedRunWithProjectionWork_spec run G D (sub _ _)).2.1
    change 2*G.card+2*cross.card+2*D.length+2*G.card*(run K (D.map (projectDemand G))).card
      +2*Fintype.card V ≤ 4*G.card+2*D.length+2*G.card^2+2*Fintype.card V at raw
    rw [← sameH] at raw
    refine ⟨?_, ?_⟩
    · change connectors G ∪ liftedArcs G H.1 = connectors G ∪ liftedArcs G (run K (D.map (projectDemand G)))
      rw [sameH]
    · exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ raw) _) H.2

private theorem condensation_card_le_input (G : Arcs V) : (condensation G).card ≤ G.card :=
  card_image_le.trans (card_le_card (filter_subset _ _))

private def forwardCoreSearchWork (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ :=
  let result := forwardRunWithSearchWork G ∅ D
  (result.1, result.2.1+result.2.2)

private theorem forwardCoreSearchWork_output (G : Arcs V) (D : List (V × V)) :
    (forwardCoreSearchWork G D).1 = forwardRun G D :=
  (forwardRunWithSearchWork_spec G ∅ D).1

/-- Bound reachability arc inspections and forward successor tests in the adaptive
pairwise run, including the original graph's projection and lift. -/
def sinkPreserverWithSearchWork (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ :=
  liftedRunWithSearchWork forwardCoreSearchWork G D

theorem sinkPreserverWithSearchWork_spec (G : Arcs V) (D : List (V × V)) :
    let n := Fintype.card V
    let result := sinkPreserverWithSearchWork G D
    result.1 = sinkPreserver G D ∧ result.2 ≤
      liftSearchWorkBound n G.card D.length + D.length*(n*G.card+2*n^2) := by
  let n := Fintype.card V
  let K := condensation G
  let T := D.map (projectDemand G)
  obtain ⟨same, work⟩ := liftedRunWithSearchWork_spec forwardCoreSearchWork forwardRun
    forwardCoreSearchWork_output (fun _ _ => forwardRunFrom_subset (empty_subset _) _) G D
  obtain ⟨_, arcs, tests⟩ := forwardRunWithSearchWork_spec K ∅ T
  have total : (forwardCoreSearchWork K T).2 ≤ D.length*(n*G.card+2*n^2) := by
    change (forwardRunWithSearchWork K ∅ T).2.1+(forwardRunWithSearchWork K ∅ T).2.2 ≤ _
    rw [arcs]
    have h := Nat.add_le_add (Nat.mul_le_mul_left T.length (Nat.mul_le_mul_left n (condensation_card_le_input G))) tests
    simpa only [n, T, List.length_map, Nat.mul_add] using h
  exact ⟨same, work.trans (Nat.add_le_add_left total _)⟩

/-- The source orientation uses exactly the same metered search on the reversed graph. -/
def sourcePreserverWithSearchWork (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ :=
  let result := sinkPreserverWithSearchWork (reverseArcs G) (D.map Prod.swap)
  (reverseArcs result.1, result.2)

theorem sourcePreserverWithSearchWork_spec (G : Arcs V) (D : List (V × V)) :
    let n := Fintype.card V
    let result := sourcePreserverWithSearchWork G D
    result.1 = sourcePreserver G D ∧ result.2 ≤
      liftSearchWorkBound n G.card D.length + D.length*(n*G.card+2*n^2) := by
  obtain ⟨same, work⟩ := sinkPreserverWithSearchWork_spec (reverseArcs G) (D.map Prod.swap)
  exact ⟨congrArg reverseArcs same, by simpa only [sourcePreserverWithSearchWork, reverseArcs_card, List.length_map] using work⟩

private def offlineCoreSearchWork (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ :=
  let result := offlinePruneWithReachCalls G D
  let n := Fintype.card V
  (result.1, result.2*(n*n^2))

private theorem offlineCoreSearchWork_output (G : Arcs V) (D : List (V × V)) :
    (offlineCoreSearchWork G D).1 = offlinePrune G D :=
  (offlinePruneWithReachCalls_spec G D).1

/-- Each pruning reachability call scans at most n² possible graph arcs
in each of the n rounds. The count includes the original SCC lift. -/
def offlinePreserverWithSearchWork (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ :=
  liftedRunWithSearchWork offlineCoreSearchWork G D

theorem offlinePreserverWithSearchWork_spec (G : Arcs V) (D : List (V × V)) :
    let n := Fintype.card V
    let result := offlinePreserverWithSearchWork G D
    result.1 = offlinePreserver G D ∧ result.2 ≤
      liftSearchWorkBound n G.card D.length + G.card*(2*D.length)*(n*n^2) := by
  let n := Fintype.card V
  let K := condensation G
  let T := D.map (projectDemand G)
  obtain ⟨same, work⟩ := liftedRunWithSearchWork_spec offlineCoreSearchWork offlinePrune
    offlineCoreSearchWork_output (fun K T => (offlinePrune_spec K T).1) G D
  have calls := (offlinePruneWithReachCalls_spec K T).2.trans
    (Nat.mul_le_mul_right (2*T.length) (condensation_card_le_input G))
  have total : (offlineCoreSearchWork K T).2 ≤ G.card*(2*D.length)*(n*n^2) := by
    simpa only [offlineCoreSearchWork, n, T, List.length_map] using Nat.mul_le_mul_right (n*n^2) calls
  exact ⟨same, work.trans (Nat.add_le_add_left total _)⟩


/-- The outputs and search work from evaluating all revealed prefixes. -/
def prefixSearchReplay {A X : Type*} (evaluate : List A → X × ℕ) (D : List A) :
    List X × ℕ :=
  let runs := D.inits.map evaluate
  (runs.map Prod.fst, (runs.map Prod.snd).sum)

theorem prefixSearchReplay_spec {A X : Type*} (evaluate : List A → X × ℕ)
    (plain : List A → X) (budget : ℕ → ℕ) (D : List A)
    (same : ∀ P, (evaluate P).1 = plain P)
    (work : ∀ P, P <+: D → (evaluate P).2 ≤ budget D.length) :
    let result := prefixSearchReplay evaluate D
    result.1 = D.inits.map plain ∧ result.2 ≤ (D.length+1)*budget D.length := by
  refine ⟨?_, ?_⟩
  · simp [prefixSearchReplay, Function.comp_def, same]
  · change ((D.inits.map evaluate).map Prod.snd).sum ≤ _
    rw [List.map_map]
    calc
      _ ≤ D.inits.length * budget D.length := by
        have each : ∀ k ∈ D.inits.map (fun P => (evaluate P).2), k ≤ budget D.length := by
          intro k hk
          obtain ⟨P, hp, rfl⟩ := List.mem_map.mp hk
          exact work P ((List.mem_inits _ _).mp hp)
        have cap := List.sum_le_length_nsmul _ _ each
        simpa only [Function.comp_def, List.length_map, nsmul_eq_mul, Nat.cast_id] using cap
      _ = _ := by rw [List.length_inits]

private theorem liftSearchWorkBound_mono (n m : ℕ) : Monotone (liftSearchWorkBound n m) := by
  intro p q le
  unfold liftSearchWorkBound
  gcongr

/-- Replaying the forward preserver on all revealed prefixes has a polynomial
search bound and exposes exactly the ordinary purchased graphs. -/
theorem sinkPreserver_prefixSearchReplay (G : Arcs V) (D : List (V × V)) :
    let n := Fintype.card V
    let p := D.length
    let result := prefixSearchReplay (sinkPreserverWithSearchWork G) D
    result.1 = D.inits.map (sinkPreserver G) ∧
      result.2 ≤ (p+1)*(liftSearchWorkBound n G.card p + p*(n*G.card+2*n^2)) := by
  apply prefixSearchReplay_spec _ _ (fun p =>
    liftSearchWorkBound (Fintype.card V) G.card p + p*(Fintype.card V*G.card+2*Fintype.card V^2))
  · intro P
    exact (sinkPreserverWithSearchWork_spec G P).1
  · intro P earlier
    exact (sinkPreserverWithSearchWork_spec G P).2.trans
      (Nat.add_le_add (liftSearchWorkBound_mono _ _ earlier.length_le)
        (Nat.mul_le_mul_right _ earlier.length_le))

end OnlineReachabilityPreservers
