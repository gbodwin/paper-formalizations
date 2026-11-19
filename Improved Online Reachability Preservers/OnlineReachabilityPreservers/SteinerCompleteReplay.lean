import OnlineReachabilityPreservers.SteinerComplete
import OnlineReachabilityPreservers.SteinerEarlyReplay
import OnlineReachabilityPreservers.SteinerLateReplay

/-! Compose measured graph searches through the actual seeded Steiner run. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

omit [Fintype V] in
private theorem distinctTrace_length_le (D : List (V × V)) : (distinctNonselfTrace D).length ≤ D.length := by
  rw [← List.toFinset_card_of_nodup (distinctNonselfTrace_nodup D)]
  exact (card_le_card (fun _ h => List.mem_toFinset.mpr (mem_distinctNonselfTrace.mp
    (List.mem_toFinset.mp h)).1)).trans (List.toFinset_card_le D)

/-- Compose exact graph outputs and search charges for all phases of one prefix. -/
def completeSteinerDrawRunWithSearchWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : Arcs V × ℕ :=
  let n := Fintype.card V
  let T := steinerEarlyCutoff n
  let P := distinctNonselfTrace D
  let early := earlyRoundedGraphWithSearchWork G height sample (P.take T)
  let late := lateSteinerWithSearchWork G (steinerThinThreshold n) (sampledVertices draw) thin (P.drop T)
  (early.1 ∪ late.1,early.2+late.2)

/-- The runtime expression bounds the measured operations on every seed.
Sampling is charged separately, as are arithmetic and container operations. -/
theorem completeSteinerDrawRunWithSearchWork_spec (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let m := G.card
    let F := Fintype.card (HeightForestVertex V height)
    let N := Fintype.card (ForestNetworkVertex V height)
    let out := completeSteinerDrawRunWithSearchWork G height sample draw thin D
    out.1 = completeSteinerDrawRun G height sample draw thin D ∧
      out.2 ≤ earlySearchWorkBound n m F N D.length+lateSearchWorkBound n m D.length := by
  let n := Fintype.card V
  let m := G.card
  let F := Fintype.card (HeightForestVertex V height)
  let N := Fintype.card (ForestNetworkVertex V height)
  let T := steinerEarlyCutoff n
  let P := distinctNonselfTrace D
  let left := earlyRoundedGraphWithSearchWork G height sample (P.take T)
  let right := lateSteinerWithSearchWork G (steinerThinThreshold n) (sampledVertices draw) thin (P.drop T)
  have plen : P.length ≤ D.length := distinctTrace_length_le D
  have earlyLen : (P.take T).length ≤ D.length := (List.take_prefix _ _).length_le.trans plen
  have lateLen : (P.drop T).length ≤ D.length := (List.drop_suffix _ _).length_le.trans plen
  have applicable : ∀ d ∈ P.drop T, Reach G d.1 d.2 :=
    fun d hd => feasible d (mem_distinctNonselfTrace.mp (List.mem_of_mem_drop hd)).1
  have first := earlyRoundedGraphWithSearchWork_spec G height sample (P.take T)
  have workForLate (rule : EarlySteinerRule G) :=
    lateSteinerWithSearchWork_spec rule (steinerThinThreshold n) (sampledVertices draw) thin (P.drop T) applicable
  change left.1 ∪ right.1 = completeSteinerDrawRun G height sample draw thin D ∧
    left.2+right.2 ≤ earlySearchWorkBound n m F N D.length+lateSearchWorkBound n m D.length
  constructor
  · unfold completeSteinerDrawRun completeSteinerRun
    exact congrArg₂ (· ∪ ·) first.1 (workForLate _).1
  · have leftBound := first.2.trans (earlySearchWorkBound_mono n m le_rfl le_rfl earlyLen)
    have rightBound : right.2 ≤ lateSearchWorkBound n m D.length := by
      exact (workForLate (earlyRoundedRule G height sample)).2.trans (lateSearchWorkBound_mono n m lateLen)
    exact Nat.add_le_add leftBound rightBound

/-- An explicit polynomial upper bound on the measured search operations
for fixed height, with the forest size and the logarithm replaced by bounds. -/
def completeSteinerSearchPolynomial (n m height p : ℕ) : ℕ :=
  let F := (n*2)*((height+1)*n^height)
  let N := 3*F
  let B := 1+n*F^2
  let routes := F^2*labelledRouteSearchBound n m
  (p+1)*(p*(((B+1)*B+1)*weightedSeparatorWorkBound N (N^2) B)+routes+n*m)+routes+
    (p*lateStepSearchWorkBound n m p+p*(2*n*m)+hubSearchWorkBound n m p+
      (p+1)*((p+m*(m+1))*thinSeparatorWorkBound n m+m+n*m))

private theorem completeSteinerSearchBound_le (n m F N height p : ℕ)
    (size : F ≤ (n*2)*((height+1)*n^height)) (net : N ≤ 3*F) :
    earlySearchWorkBound n m F N p+lateSearchWorkBound n m p ≤ completeSteinerSearchPolynomial n m height p := by
  let F' := (n*2)*((height+1)*n^height)
  let N' := 3*F'
  let B := 1+n*F'^2
  let routes := F'^2*labelledRouteSearchBound n m
  have net' : N ≤ N' := net.trans (Nat.mul_le_mul_left _ size)
  have scale : max 1 (n*F'^2) ≤ B := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  unfold completeSteinerSearchPolynomial
  apply Nat.add_le_add
  · refine (earlySearchWorkBound_mono n m size net' le_rfl).trans ?_
    change earlySearchWorkBound n m F' N' p ≤
      (p+1)*(p*(((B+1)*B+1)*weightedSeparatorWorkBound N' (N'^2) B)+routes+n*m)+routes
    unfold earlySearchWorkBound earlyPrefixSearchWorkBound routes weightedSeparatorWorkBound
    dsimp only
    gcongr
  · unfold lateSearchWorkBound thinRoundPrefixWorkBound
    gcongr
    exact Nat.log2_le_self _

theorem completeSteinerDrawRunWithSearchWork_polynomial (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (completeSteinerDrawRunWithSearchWork G height sample draw thin D).2 ≤
      completeSteinerSearchPolynomial (Fintype.card V) G.card height D.length := by
  have size : Fintype.card (HeightForestVertex V height) ≤
      (Fintype.card V*2)*((height+1)*Fintype.card V^height) := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr ne => exact heightForestVertex_card_le V height
  have net : Fintype.card (ForestNetworkVertex V height) ≤
      3*Fintype.card (HeightForestVertex V height) := by
    simp [ForestNetworkVertex]
  exact (completeSteinerDrawRunWithSearchWork_spec G height sample draw thin D feasible).2.trans
    (completeSteinerSearchBound_le _ _ _ _ _ _ size net)

/-- Evaluate all prefixes in arrival order with the same seeds. -/
def completeSteinerPrefixSearchReplay (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : List (Arcs V × ℕ) :=
  D.inits.map (completeSteinerDrawRunWithSearchWork G height sample draw thin)

private theorem completeSteinerSearchPolynomial_mono (n m height : ℕ) :
    Monotone (completeSteinerSearchPolynomial n m height) := by
  intro p q le
  unfold completeSteinerSearchPolynomial lateStepSearchWorkBound hubSearchWorkBound liftSearchWorkBound
  dsimp only
  gcongr

theorem completeSteinerPrefixSearchReplay_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeSteinerPrefixSearchReplay G height sample draw thin D
    out.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.map Prod.snd).sum ≤ (D.length+1)*completeSteinerSearchPolynomial (Fintype.card V) G.card height D.length := by
  let C := completeSteinerSearchPolynomial (Fintype.card V) G.card height
  dsimp only [completeSteinerPrefixSearchReplay]
  constructor
  · rw [List.map_map]
    apply List.map_congr_left
    intro P member
    have pref := (List.mem_inits _ _).mp member
    exact (completeSteinerDrawRunWithSearchWork_spec G height sample draw thin P
      (fun d hd => feasible d (pref.subset hd))).1
  · rw [List.map_map]
    let work (P : List (V × V)) := (completeSteinerDrawRunWithSearchWork G height sample draw thin P).2
    have each (P : List (V × V)) (member : P ∈ D.inits) :
        work P ≤ C D.length := by
      have pref := (List.mem_inits _ _).mp member
      exact (completeSteinerDrawRunWithSearchWork_polynomial G height sample draw thin P
        (fun d hd => feasible d (pref.subset hd))).trans
        (completeSteinerSearchPolynomial_mono _ _ _ pref.length_le)
    have sum_le (L : List (List (V × V))) (bounded : ∀ P ∈ L, work P ≤ C D.length) :
        (L.map work).sum ≤ (L.map fun _ => C D.length).sum := by
      induction L with
      | nil => simp
      | cons P L ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (bounded P List.mem_cons_self)
          (ih (fun Q present => bounded Q (List.mem_cons_of_mem _ present)))
    change (D.inits.map work).sum ≤ _
    calc
      _ ≤ (D.inits.map (fun _ => C D.length)).sum := sum_le _ each
      _ = (D.length+1)*C D.length := by simp

end OnlineReachabilityPreservers
