import OnlineReachabilityPreservers.SearchWork
import OnlineReachabilityPreservers.SteinerThinCover

/-! Search work in choosing SCC labels and shortest original routes. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Count arc inspections in the two reverse searches of an SCC label. -/
def componentLabelWithSearchWork (G : Arcs V) (v : V) : V × ℕ :=
  let n := Fintype.card V
  let inward := reachInWithArcInspections G v n
  let outward := reachInWithArcInspections (reverseArcs G) v n
  ((least? (inward.1 ∩ outward.1)).getD v, inward.2 + outward.2)

theorem componentLabelWithSearchWork_spec (G : Arcs V) (v : V) :
    componentLabelWithSearchWork G v = (componentLabel G v, 2 * Fintype.card V * G.card) := by
  simp only [componentLabelWithSearchWork, reachInWithArcInspections_spec, componentLabel, componentVertices,
    reaches, reverseArcs_card, Prod.mk.injEq, true_and]
  ring

private def hopsWorkEntry (G : Arcs V) (s t : V) (depth : ℕ) : ℕ × Bool × ℕ :=
  let result := reachInWithArcInspections G t depth
  (depth, decide (s ∈ result.1), result.2)

/-- Count arc inspections in every tested hop depth, retaining each result once. -/
def hopsWithSearchWork (G : Arcs V) (s t : V) : ℕ × ℕ :=
  let n := Fintype.card V
  let entries := (range (n + 1)).image (hopsWorkEntry G s t)
  let successful := (entries.filter (fun entry => entry.2.1 = true)).image Prod.fst
  ((least? successful).getD (n + 1), ∑ entry ∈ entries, entry.2.2)

theorem hopsWithSearchWork_spec (G : Arcs V) (s t : V) :
    let result := hopsWithSearchWork G s t
    let n := Fintype.card V
    result.1 = hops G s t ∧ result.2 ≤ (n + 1) * n * G.card := by
  let candidates := range (Fintype.card V + 1)
  let entry := hopsWorkEntry G s t
  have passes (k : ℕ) : (entry k).2.1 = true ↔ s ∈ reachIn G t k := by
    simp [entry, hopsWorkEntry, reachInWithArcInspections_spec]
  refine ⟨?_, ?_⟩
  · have same : ((candidates.image entry).filter (fun x => x.2.1 = true)).image Prod.fst =
        candidates.filter (fun k => s ∈ reachIn G t k) := by
      ext k
      constructor
      · intro h
        obtain ⟨value, hvalue, hd⟩ := mem_image.mp h
        obtain ⟨hvalue, passed⟩ := mem_filter.mp hvalue
        obtain ⟨depth, inside, rfl⟩ := mem_image.mp hvalue
        change depth = k at hd
        subst depth
        exact mem_filter.mpr ⟨inside, (passes k).mp passed⟩
      · intro h
        obtain ⟨inside, passed⟩ := mem_filter.mp h
        exact mem_image.mpr ⟨entry k, mem_filter.mpr ⟨mem_image_of_mem _ inside, (passes k).mpr passed⟩, rfl⟩
    exact congrArg (fun S => (least? S).getD (Fintype.card V + 1)) same
  · change (∑ x ∈ candidates.image entry, x.2.2) ≤ _
    rw [sum_image (fun a _ b _ eq => congrArg Prod.fst eq)]
    calc
      _ ≤ ∑ _ ∈ candidates, Fintype.card V * G.card := by
        apply sum_le_sum
        intro k hk
        simpa [entry, hopsWorkEntry, reachInWithArcInspections_spec] using
          Nat.mul_le_mul_right G.card (Nat.le_of_lt_succ (mem_range.mp hk))
      _ = _ := by simp [candidates, Nat.mul_assoc]

private def routeArcWorkEntry (G : Arcs V) (t : V) (e : V × V) : (V × V) × Bool × ℕ :=
  let source := hopsWithSearchWork G e.1 t
  let target := hopsWithSearchWork G e.2 t
  (e, decide (target.1 < source.1), source.2 + target.2)

/-- Meter the hop tests and the subsequent search without changing
the selected shortest route. -/
def routePathWithSearchWork (G : Arcs V) (s t : V) :
    Option (List (V × V)) × ℕ × ℕ :=
  let checked := G.image (routeArcWorkEntry G t)
  let H := (checked.filter (fun entry => entry.2.1 = true)).image Prod.fst
  let tail := forwardPathWithSearchWork H ∅ s t
  (tail.1, (∑ entry ∈ checked, entry.2.2) + tail.2.1, tail.2.2)

theorem routePathWithSearchWork_spec (G : Arcs V) (s t : V) :
    let result := routePathWithSearchWork G s t
    let n := Fintype.card V
    result.1 = routePath G s t ∧
      result.2.1 ≤ G.card * (2 * ((n + 1) * n * G.card)) + n * G.card ∧ result.2.2 ≤ 2 * n^2 := by
  let n := Fintype.card V
  let entry := routeArcWorkEntry G t
  let H := ((G.image entry).filter (fun x => x.2.1 = true)).image Prod.fst
  have passes (e : V × V) : (entry e).2.1 = true ↔ hops G e.2 t < hops G e.1 t := by
    simp [entry, routeArcWorkEntry, (hopsWithSearchWork_spec G e.1 t).1,
      (hopsWithSearchWork_spec G e.2 t).1]
  have same : H = G.filter (fun e => hops G e.2 t < hops G e.1 t) := by
    ext e
    constructor
    · intro h
      obtain ⟨value, hvalue, he⟩ := mem_image.mp h
      obtain ⟨hvalue, passed⟩ := mem_filter.mp hvalue
      obtain ⟨f, inside, rfl⟩ := mem_image.mp hvalue
      change f = e at he
      subst f
      exact mem_filter.mpr ⟨inside, (passes e).mp passed⟩
    · intro h
      obtain ⟨inside, passed⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨entry e, mem_filter.mpr ⟨mem_image_of_mem _ inside, (passes e).mpr passed⟩, rfl⟩
  have arcCap : H.card ≤ G.card := by rw [same]; exact card_le_card (filter_subset _ _)
  have sumBound : (∑ x ∈ G.image entry, x.2.2) ≤ G.card * (2 * ((n + 1) * n * G.card)) := by
    rw [sum_image (fun a _ b _ eq => congrArg Prod.fst eq)]
    calc
      _ ≤ ∑ _ ∈ G, 2 * ((n + 1) * n * G.card) := by
        apply sum_le_sum
        intro e _
        rw [two_mul]
        exact Nat.add_le_add (hopsWithSearchWork_spec G e.1 t).2 (hopsWithSearchWork_spec G e.2 t).2
      _ = _ := by simp
  obtain ⟨path, reachWork, successorWork⟩ := forwardPathWithSearchWork_spec H ∅ s t
  change (forwardPathWithSearchWork H ∅ s t).1 = routePath G s t ∧
    (∑ x ∈ G.image entry, x.2.2) + (forwardPathWithSearchWork H ∅ s t).2.1 ≤ _ ∧ _
  refine ⟨path.trans ?_, ?_, successorWork⟩
  · rw [same]
    rfl
  · rw [reachWork]
    exact Nat.add_le_add sumBound (Nat.mul_le_mul_left _ arcCap)

/-- Count label calls in projection and lifting. Include allowances for
one hop search and one bounded-depth search per vertex in each connector
orientation. The condensed algorithm runs once and its internal work
is outside these counts. -/
def liftedRunWithProjectionWork (run : Arcs V → List (V × V) → Arcs V)
    (G : Arcs V) (D : List (V × V)) : Arcs V × ℕ × ℕ × ℕ :=
  match D with
  | [] => (∅, 0, 0, 0)
  | _ :: _ =>
    let crossing := G.filter (fun e => componentLabel G e.1 ≠ componentLabel G e.2)
    let H := run (crossing.image (projectDemand G)) (D.map (projectDemand G))
    let n := Fintype.card V
    (connectors G ∪ liftedArcs G H,
      2 * G.card + 2 * crossing.card + 2 * D.length + 2 * G.card * H.card + 2 * n,
      2 * n, 2 * n)

theorem liftedRunWithProjectionWork_spec (run : Arcs V → List (V × V) → Arcs V)
    (G : Arcs V) (D : List (V × V))
    (inside : run (condensation G) (D.map (projectDemand G)) ⊆ condensation G) :
    let result := liftedRunWithProjectionWork run G D
    let n := Fintype.card V
    result.1 = liftedRun run G D ∧
      result.2.1 ≤ 4 * G.card + 2 * D.length + 2 * G.card ^ 2 + 2 * n ∧
      result.2.2.1 ≤ 2 * n ∧ result.2.2.2 ≤ 2 * n := by
  cases D with
  | nil => simp [liftedRunWithProjectionWork, liftedRun]
  | cons d rest =>
    let D := d :: rest
    let crossing := G.filter (fun e => componentLabel G e.1 ≠ componentLabel G e.2)
    let H := run (crossing.image (projectDemand G)) (D.map (projectDemand G))
    have crossingBound : crossing.card ≤ G.card := card_le_card (filter_subset _ _)
    have between : (condensation G).card ≤ G.card := card_image_le.trans crossingBound
    have sub : H.card ≤ G.card := (card_le_card inside).trans between
    have grow :
        2 * G.card + 2 * crossing.card + 2 * D.length + 2 * G.card * H.card + 2 * Fintype.card V ≤
          2 * G.card + 2 * G.card + 2 * D.length + 2 * G.card * G.card + 2 * Fintype.card V := by
      gcongr
    exact ⟨rfl, grow.trans_eq (by ring), le_rfl, le_rfl⟩

/-- Replay the actual forward steps and add their search work. -/
def forwardRunWithSearchWork (G : Arcs V) : Arcs V → List (V × V) → Arcs V × ℕ × ℕ
  | H, [] => (H, 0, 0)
  | H, d :: D =>
    let step := forwardPathWithSearchWork G H d.1 d.2
    let tail := forwardRunWithSearchWork G (H ∪ (step.1.getD []).toFinset) D
    (tail.1, step.2.1 + tail.2.1, step.2.2 + tail.2.2)

theorem forwardRunWithSearchWork_spec (G H : Arcs V) (D : List (V × V)) :
    let n := Fintype.card V
    let result := forwardRunWithSearchWork G H D
    result.1 = forwardRunFrom G H D ∧ result.2.1 = D.length * (n * G.card) ∧
      result.2.2 ≤ D.length * (2 * n ^ 2) := by
  induction D generalizing H with
  | nil => simp [forwardRunWithSearchWork, forwardRunFrom]
  | cons d D ih =>
    let step := forwardPathWithSearchWork G H d.1 d.2
    let next := H ∪ (step.1.getD []).toFinset
    obtain ⟨path, scans, count⟩ := forwardPathWithSearchWork_spec G H d.1 d.2
    change step.1 = _ at path
    change step.2.1 = _ at scans
    change step.2.2 ≤ _ at count
    have same : next = forwardStep G H d := by simp [next, path, forwardStep, forwardEdges]
    obtain ⟨endResult, endScans, endCount⟩ := ih next
    refine ⟨endResult.trans (congrArg (fun K => forwardRunFrom G K D) same), ?_, ?_⟩
    · change step.2.1 + (forwardRunWithSearchWork G next D).2.1 = _
      rw [scans, endScans, List.length_cons, Nat.succ_mul]
      exact Nat.add_comm _ _
    · change step.2.2 + (forwardRunWithSearchWork G next D).2.2 ≤ _
      rw [List.length_cons, Nat.succ_mul]
      exact (Nat.add_le_add count endCount).trans_eq (Nat.add_comm _ _)

/-- Meter the cut separator calls in a thin capacity update. -/
def thinCoverLoopWithCalls (G : Arcs V) (d : V × V) : ℕ → CutLoads V → (CutLoads V × ℕ) × ℕ
  | 0, load => ((load, 0), 0)
  | fuel + 1, load =>
    match fastThinViolation G d load with
    | none => ((load, 0), 1)
    | some W =>
      let result := thinCoverLoopWithCalls G d fuel (doubleCut (outgoingCut (intervalArcs G d) W) load)
      ((result.1.1, result.1.2 + 1), result.2 + 1)

theorem thinCoverLoopWithCalls_spec (G : Arcs V) (d : V × V) (fuel : ℕ) (load : CutLoads V) :
    let result := thinCoverLoopWithCalls G d fuel load
    result.1 = thinCoverLoop G d fuel load ∧ result.2 ≤ fuel := by
  induction fuel generalizing load with
  | zero => simp [thinCoverLoopWithCalls, thinCoverLoop]
  | succ fuel ih =>
    cases check : fastThinViolation G d load with
    | none => simp [thinCoverLoopWithCalls, thinCoverLoop, check]
    | some W =>
      obtain ⟨out, calls⟩ := ih (doubleCut (outgoingCut (intervalArcs G d) W) load)
      simp only [thinCoverLoopWithCalls, thinCoverLoop, check, out, true_and]
      exact Nat.succ_le_succ calls

private def thinCoverRunWithCallsFrom (G : Arcs V) :
    List (V × V) → CutLoads V → CutLoads V × ℕ
  | [], load => (load, 0)
  | d :: D, load =>
    let first := thinCoverLoopWithCalls G d (G.card * (G.card.log2 + 1) + 1) load
    let tail := thinCoverRunWithCallsFrom G D first.1.1
    (tail.1, first.2 + tail.2)

private theorem thinCoverRunWithCallsFrom_spec (G : Arcs V) (D : List (V × V)) (initial : CutLoads V) :
    let result := thinCoverRunWithCallsFrom G D initial
    result.1 = D.foldl (fun load d => thinCoverStep G d load) initial ∧
      result.2 ≤ D.length * (G.card * (G.card.log2 + 1) + 1) := by
  induction D generalizing initial with
  | nil => simp [thinCoverRunWithCallsFrom]
  | cons d D ih =>
    let fuel := G.card * (G.card.log2 + 1) + 1
    let first := thinCoverLoopWithCalls G d fuel initial
    obtain ⟨startEq, startBound⟩ := thinCoverLoopWithCalls_spec G d fuel initial
    obtain ⟨endEq, endBound⟩ := ih first.1.1
    change (thinCoverRunWithCallsFrom G D first.1.1).1 =
      D.foldl (fun load d => thinCoverStep G d load) (thinCoverStep G d initial) ∧
      first.2 + (thinCoverRunWithCallsFrom G D first.1.1).2 ≤ (D.length + 1) * fuel
    have same : first.1.1 = thinCoverStep G d initial := congrArg Prod.fst startEq
    refine ⟨endEq.trans (congrArg (D.foldl (fun load d => thinCoverStep G d load)) same), ?_⟩
    exact (Nat.add_le_add startBound endBound).trans_eq
      ((Nat.add_comm _ _).trans (Nat.succ_mul D.length fuel).symm)

/-- The thin fractional run with its separator-call budget. -/
def thinCoverRunWithCalls (G : Arcs V) (D : List (V × V)) : CutLoads V × ℕ :=
  thinCoverRunWithCallsFrom G D (fun _ => 0)

theorem thinCoverRunWithCalls_spec (G : Arcs V) (D : List (V × V)) :
    let result := thinCoverRunWithCalls G D
    result.1 = thinCoverRun G D ∧ result.2 ≤ D.length * (G.card * (G.card.log2 + 1) + 1) :=
  thinCoverRunWithCallsFrom_spec G D _

end OnlineReachabilityPreservers
