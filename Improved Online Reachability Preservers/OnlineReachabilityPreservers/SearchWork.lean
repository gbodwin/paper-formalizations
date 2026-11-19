import OnlineReachabilityPreservers.Growth
import OnlineReachabilityPreservers.SteinerForestNetwork

/-! Count finite search-loop operations with the same outputs as the
unmetered searches. An arc inspection is one visit in a filter over the
arc set. A successor test checks one candidate in either priority list. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V]

/-- The ordinary reverse search, reporting the number of input-arc inspections. -/
def reachInWithArcInspections (G : Arcs V) (t : V) : ℕ → Finset V × ℕ
  | 0 => ({t}, 0)
  | k + 1 =>
    let prev := reachInWithArcInspections G t k
    (prev.1 ∪ (G.filter fun e => e.2 ∈ prev.1).image Prod.fst, prev.2 + G.card)

theorem reachInWithArcInspections_spec (G : Arcs V) (t : V) (k : ℕ) :
    reachInWithArcInspections G t k = (reachIn G t k, k * G.card) := by
  induction k with
  | zero => simp [reachInWithArcInspections, reachIn]
  | succ k ih => simp [reachInWithArcInspections, reachIn, ih, Nat.succ_mul]

/-- Charge both priority-list filters whenever the walk search tests a
vertex. A failed search carries its count as well. -/
def growFromWithSuccessorTests (G H : Arcs V) (R : Finset V) (t : V) :
    ℕ → V → Option (List (V × V)) × ℕ
  | 0, u => (if u = t then some [] else none, 0)
  | k + 1, u =>
    if u = t then (some [], 0)
    else
      match nextVertex G H R u with
      | none => (none, 2 * R.card)
      | some v =>
        let rest := growFromWithSuccessorTests G H R t k v
        (rest.1.map ((u, v) :: ·), rest.2 + 2 * R.card)

theorem growFromWithSuccessorTests_spec (G H : Arcs V) (R : Finset V) (t : V) (k : ℕ) (u : V) :
    let result := growFromWithSuccessorTests G H R t k u
    result.1 = growFrom G H R t k u ∧ result.2 ≤ k * (2 * R.card) := by
  induction k generalizing u with
  | zero => simp [growFromWithSuccessorTests, growFrom]
  | succ k ih =>
    by_cases equal : u = t
    · simp [growFromWithSuccessorTests, growFrom, equal]
    cases found : nextVertex G H R u with
    | none =>
      simp only [growFromWithSuccessorTests, growFrom, equal, found, ↓reduceIte]
      refine ⟨rfl, ?_⟩
      rw [Nat.succ_mul k (2 * R.card)]
      exact Nat.le_add_left _ _
    | some v =>
      obtain ⟨output, count⟩ := ih v
      simp only [growFromWithSuccessorTests, growFrom, equal, found, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · change ((growFromWithSuccessorTests G H R t k v).1).map ((u, v) :: ·) =
          (growFrom G H R t k v).bind (fun tail => some ((u, v) :: tail))
        rw [← output]
        cases (growFromWithSuccessorTests G H R t k v).1 <;> rfl
      · exact (Nat.add_le_add_right count _).trans_eq (Nat.succ_mul _ _).symm

variable [Fintype V]

/-- The first field is the original output. The remaining fields count
reverse-search arc inspections and greedy successor tests. -/
def forwardPathWithSearchWork (G H : Arcs V) (s t : V) : Option (List (V × V)) × ℕ × ℕ :=
  let n := Fintype.card V
  let reverseSearch := reachInWithArcInspections G t n
  let walkSearch := growFromWithSuccessorTests G H reverseSearch.1 t n s
  (walkSearch.1, reverseSearch.2, walkSearch.2)

theorem forwardPathWithSearchWork_spec (G H : Arcs V) (s t : V) :
    let result := forwardPathWithSearchWork G H s t
    let n := Fintype.card V
    result.1 = forwardPath G H s t ∧ result.2.1 = n * G.card ∧ result.2.2 ≤ 2 * n ^ 2 := by
  simp only [forwardPathWithSearchWork, reachInWithArcInspections_spec, forwardPath, reaches]
  obtain ⟨output, count⟩ :=
    growFromWithSuccessorTests_spec G H (reaches G t) t (Fintype.card V) s
  refine ⟨output, True.intro, count.trans ?_⟩
  calc
    _ ≤ Fintype.card V * (2 * Fintype.card V) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_le_univ _))
    _ = _ := by ring

section Cover

variable {E : Type*} [DecidableEq E]

/-- A bounded weighted cutting loop with its number of separator calls. -/
def weightedCoverLoopWithCalls (search : (E → ℕ) → Option (Finset E)) :
    ℕ → (E → ℕ) → ((E → ℕ) × List (Finset E)) × ℕ
  | 0, charges => ((charges, []), 0)
  | fuel + 1, charges =>
    match search charges with
    | none => ((charges, []), 1)
    | some cut =>
      let out := weightedCoverLoopWithCalls search fuel (chargeWeightedCut cut charges)
      ((out.1.1, cut :: out.1.2), out.2 + 1)

theorem weightedCoverLoopWithCalls_spec (search : (E → ℕ) → Option (Finset E))
    (fuel : ℕ) (charges : E → ℕ) :
    let result := weightedCoverLoopWithCalls search fuel charges
    result.1 = weightedCoverLoop search fuel charges ∧ result.2 ≤ fuel := by
  induction fuel generalizing charges with
  | zero => simp [weightedCoverLoopWithCalls, weightedCoverLoop]
  | succ fuel ih =>
    cases answer : search charges with
    | none => simp [weightedCoverLoopWithCalls, weightedCoverLoop, answer]
    | some cut =>
      obtain ⟨out, count⟩ := ih (chargeWeightedCut cut charges)
      simp only [weightedCoverLoopWithCalls, weightedCoverLoop, answer, out, true_and]
      exact Nat.succ_le_succ count

end Cover

/-- Report every residual path search, including the final failed search. -/
def unitAugmentationsWithPathCalls (c : ArcFlow V) (s t : V) :
    ℕ → ArcFlow V → (ArcFlow V × ℕ) × ℕ
  | 0, f => ((f, 0), 0)
  | k + 1, f =>
    match routePath (residualArcs c f) s t with
    | none => ((f, 0), 1)
    | some path =>
      let out := unitAugmentationsWithPathCalls c s t k (augmentArcFlow f path.toFinset)
      ((out.1.1, out.1.2 + 1), out.2 + 1)

theorem unitAugmentationsWithPathCalls_spec (c : ArcFlow V) (s t : V) (fuel : ℕ) (f : ArcFlow V) :
    let result := unitAugmentationsWithPathCalls c s t fuel f
    result.1 = unitAugmentations c s t fuel f ∧ result.2 ≤ fuel := by
  induction fuel generalizing f with
  | zero => simp [unitAugmentationsWithPathCalls, unitAugmentations]
  | succ fuel ih =>
    cases route : routePath (residualArcs c f) s t with
    | none => simp [unitAugmentationsWithPathCalls, unitAugmentations, route]
    | some path =>
      obtain ⟨output, calls⟩ := ih (augmentArcFlow f path.toFinset)
      simp only [unitAugmentationsWithPathCalls, unitAugmentations, route, output, true_and]
      exact Nat.succ_le_succ calls

/-- Execute the same sequence of weighted network updates while counting
separation calls. There is no charge for the empty request list. -/
def weightedNetworkRunWithCalls (edges : Arcs V) (weight : V × V → ℕ) :
    List (WeightedNetworkDemand V) → (V × V → ℕ) → ((V × V → ℕ) × List (Arcs V)) × ℕ
  | [], initial => ((initial, []), 0)
  | d :: rest, initial =>
    let first := weightedCoverLoopWithCalls
      (weightedNetworkViolation edges d weight (weightedCoverScale edges weight))
      (weightedCoverFuel edges weight) initial
    let last := weightedNetworkRunWithCalls edges weight rest first.1.1
    ((last.1.1, first.1.2 ++ last.1.2), first.2 + last.2)

theorem weightedNetworkRunWithCalls_spec (edges : Arcs V) (weight : V × V → ℕ)
    (D : List (WeightedNetworkDemand V)) (initial : V × V → ℕ) :
    let result := weightedNetworkRunWithCalls edges weight D initial
    result.1 = weightedNetworkRun edges weight D initial ∧
      result.2 ≤ D.length * weightedCoverFuel edges weight := by
  induction D generalizing initial with
  | nil => simp [weightedNetworkRunWithCalls, weightedNetworkRun]
  | cons d D ih =>
    let first := weightedCoverLoopWithCalls
      (weightedNetworkViolation edges d weight (weightedCoverScale edges weight))
      (weightedCoverFuel edges weight) initial
    obtain ⟨same, budget⟩ := weightedCoverLoopWithCalls_spec
      (weightedNetworkViolation edges d weight (weightedCoverScale edges weight))
      (weightedCoverFuel edges weight) initial
    change first.1 = weightedNetworkStep edges weight d initial at same
    change first.2 ≤ weightedCoverFuel edges weight at budget
    obtain ⟨tail, more⟩ := ih first.1.1
    change ((weightedNetworkRunWithCalls edges weight D first.1.1).1.1,
        first.1.2 ++ (weightedNetworkRunWithCalls edges weight D first.1.1).1.2) =
          (weightedNetworkRun edges weight (d :: D) initial) ∧
      first.2 + (weightedNetworkRunWithCalls edges weight D first.1.1).2 ≤
        (D.length + 1) * weightedCoverFuel edges weight
    refine ⟨?_, ?_⟩
    · rw [tail, same]
      rfl
    · exact (Nat.add_le_add budget more).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul D.length (weightedCoverFuel edges weight)).symm)

/-- Instantiate the same separation-call ledger on the paired forest. -/
def forestFractionalRunWithCalls (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    (((ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) ×
      List (Arcs (ForestNetworkVertex V height)))) × ℕ :=
  weightedNetworkRunWithCalls (forestNetworkPriced G (heightForest G height)) (forestNetworkWeight G)
    (D.map (forestNetworkDemand G height)) (fun _ => 0)

theorem forestFractionalRunWithCalls_spec (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    let bound := max 1 (Fintype.card V * Fintype.card (HeightForestVertex V height) ^ 2)
    let result := forestFractionalRunWithCalls G height D
    result.1 = forestFractionalRun G height D ∧ result.2 ≤ D.length * ((bound + 1) * bound + 1) := by
  let edges := forestNetworkPriced G (heightForest G height)
  let weight := forestNetworkWeight (height := height) G
  let W := weightedCoverScale edges weight
  let bound := max 1 (Fintype.card V * Fintype.card (HeightForestVertex V height) ^ 2)
  have Wle : W ≤ bound := forestNetworkScale_le G height
  obtain ⟨equal, calls⟩ := weightedNetworkRunWithCalls_spec edges weight (D.map (forestNetworkDemand G height))
    (fun _ => 0)
  refine ⟨equal, ?_⟩
  rw [List.length_map] at calls
  refine calls.trans (Nat.mul_le_mul_left _ ?_)
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul
  · exact Nat.succ_le_succ ((Nat.log2_le_self _).trans Wle)
  · exact (le_max_right _ _).trans Wle

end OnlineReachabilityPreservers
