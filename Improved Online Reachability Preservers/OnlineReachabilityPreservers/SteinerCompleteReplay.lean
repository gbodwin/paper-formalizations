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

/-- Compose the early evaluator with the ordinary split and late graph searches. -/
def completeSteinerDrawRunWithSearchWorkFromEarly (G : Arcs V)
    (early : List (V × V) → Arcs V × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : Arcs V × ℕ :=
  let n := Fintype.card V
  let T := steinerEarlyCutoff n
  let P := distinctNonselfTrace D
  let first := early (P.take T)
  let late := lateSteinerWithSearchWork G (steinerThinThreshold n) (sampledVertices draw) thin (P.drop T)
  (first.1 ∪ late.1,first.2+late.2)

/-- Compose exact graph outputs and search charges for all phases of one prefix. -/
def completeSteinerDrawRunWithSearchWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : Arcs V × ℕ :=
  completeSteinerDrawRunWithSearchWorkFromEarly G (earlyRoundedGraphWithSearchWork G height sample)
    draw thin D

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

/-- Changing the price of an early metric prefix preserves the complete
graphs and accumulates at most one early-prefix budget per call. -/
theorem completeSteinerPrefixSearchReplayFromEarly_compareOnLengths (G : Arcs V)
    (original updated : List (V × V) → Arcs V × ℕ) (K : ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V))
    (compare : ∀ P : List (V × V), P.length ≤ D.length →
      (updated P).1 = (original P).1 ∧ (updated P).2 ≤ (original P).2+(P.length+1)*K) :
    let old := D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G original draw thin)
    let out := D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G updated draw thin)
    out.map Prod.fst = old.map Prod.fst ∧
      (out.map Prod.snd).sum ≤ (old.map Prod.snd).sum+(D.length+1)*((D.length+1)*K) := by
  let old := completeSteinerDrawRunWithSearchWorkFromEarly G original draw thin
  let new := completeSteinerDrawRunWithSearchWorkFromEarly G updated draw thin
  let extra := (D.length+1)*K
  have each (P : List (V × V)) (short : P.length ≤ D.length) : (new P).1 = (old P).1 ∧
      (new P).2 ≤ (old P).2+(P.length+1)*K := by
    let trace := distinctNonselfTrace P
    let cut := steinerEarlyCutoff (Fintype.card V)
    have length := (List.take_prefix cut trace).length_le.trans (distinctTrace_length_le P)
    obtain ⟨graph,work⟩ := compare (trace.take cut) (length.trans short)
    refine ⟨?_,?_⟩
    · let late := lateSteinerWithSearchWork G (steinerThinThreshold (Fintype.card V))
        (sampledVertices draw) thin (trace.drop cut)
      exact congrArg (fun A => A ∪ late.1) graph
    · have extra := work.trans (by gcongr : (original (trace.take cut)).2+((trace.take cut).length+1)*K ≤
          (original (trace.take cut)).2+(P.length+1)*K)
      have bound := Nat.add_le_add_right extra
        (lateSteinerWithSearchWork G (steinerThinThreshold (Fintype.card V)) (sampledVertices draw) thin (trace.drop cut)).2
      simpa only [new,old,completeSteinerDrawRunWithSearchWorkFromEarly,add_right_comm] using bound
  constructor
  · change ((D.inits.map new).map Prod.fst) = (D.inits.map old).map Prod.fst
    rw [List.map_map,List.map_map]
    exact List.map_congr_left (fun P h => (each P ((List.mem_inits _ _).mp h).length_le).1)
  · have addUp (L : List (List (V × V))) (inside : ∀ P ∈ L, P ∈ D.inits) :
        (L.map (fun P => (new P).2)).sum ≤ (L.map (fun P => (old P).2)).sum+L.length*extra := by
      induction L with
      | nil => simp
      | cons P L ih =>
        have pref := (List.mem_inits _ _).mp (inside P List.mem_cons_self)
        have smaller : (P.length+1)*K ≤ extra := Nat.mul_le_mul_right K (Nat.succ_le_succ pref.length_le)
        have enough := (each P pref.length_le).2.trans (Nat.add_le_add_left smaller _)
        have later := ih (fun Q h => inside Q (List.mem_cons_of_mem _ h))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
        omega
    change ((D.inits.map new).map Prod.snd).sum ≤ ((D.inits.map old).map Prod.snd).sum+_
    rw [List.map_map,List.map_map]
    change (D.inits.map (fun P => (new P).2)).sum ≤ (D.inits.map (fun P => (old P).2)).sum+(D.length+1)*extra
    simpa only [List.length_inits] using addUp D.inits (fun _ h => h)

theorem completeSteinerPrefixSearchReplayFromEarly_compare (G : Arcs V)
    (original updated : List (V × V) → Arcs V × ℕ) (K : ℕ)
    (compare : ∀ P, (updated P).1 = (original P).1 ∧ (updated P).2 ≤ (original P).2+(P.length+1)*K)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V)) :
    let old := D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G original draw thin)
    let out := D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G updated draw thin)
    out.map Prod.fst = old.map Prod.fst ∧
      (out.map Prod.snd).sum ≤ (old.map Prod.snd).sum+(D.length+1)*((D.length+1)*K) :=
  completeSteinerPrefixSearchReplayFromEarly_compareOnLengths G original updated K draw thin D (fun P _ => compare P)

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
