import OnlineReachabilityPreservers.AlgorithmSearchWork
import OnlineReachabilityPreservers.SteinerAssembly
import OnlineReachabilityPreservers.SteinerThinReplay

/-! Compose the search charges for classification, hubs and thin rounding. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

open Finset

/-- Charge both projected preserver runs and the shared hub checks. -/
def hubSearchWorkBound (n m p : ℕ) : ℕ :=
  p*(2*n*m)+2*(liftSearchWorkBound n m p + p*(n*m+2*n^2))

private theorem hubSearchWorkBound_mono (n m : ℕ) : Monotone (hubSearchWorkBound n m) := by
  intro p q le
  unfold hubSearchWorkBound liftSearchWorkBound
  gcongr

def hubPreserverWithSearchWork (G : Arcs V) (S : Finset V) (D : List (V × V)) : Arcs V × ℕ :=
  let hits := hitRequests G S D
  let left := sinkPreserverWithSearchWork G (hits.map Prod.fst)
  let right := sourcePreserverWithSearchWork G (hits.map Prod.snd)
  (left.1 ∪ right.1, D.length*(2*Fintype.card V*G.card)+left.2+right.2)

theorem hubPreserverWithSearchWork_spec (G : Arcs V) (S : Finset V) (D : List (V × V)) :
    let out := hubPreserverWithSearchWork G S D
    out.1 = hubPreserver G S D ∧
      out.2 ≤ hubSearchWorkBound (Fintype.card V) G.card D.length := by
  let P := hitRequests G S D
  let n := Fintype.card V
  let m := G.card
  let bound (p : ℕ) := liftSearchWorkBound n m p + p*(n*m+2*n^2)
  have mono : Monotone bound := by
    intro p q le
    unfold bound liftSearchWorkBound
    gcongr
  have len : P.length ≤ D.length := List.length_filterMap_le _ D
  obtain ⟨left, lw⟩ := sinkPreserverWithSearchWork_spec G (P.map Prod.fst)
  obtain ⟨right, rw⟩ := sourcePreserverWithSearchWork_spec G (P.map Prod.snd)
  have l : (sinkPreserverWithSearchWork G (P.map Prod.fst)).2 ≤ bound D.length :=
    lw.trans (mono (by simpa only [List.length_map] using len))
  have r : (sourcePreserverWithSearchWork G (P.map Prod.snd)).2 ≤ bound D.length :=
    rw.trans (mono (by simpa only [List.length_map] using len))
  refine ⟨congrArg₂ (· ∪ ·) left right, ?_⟩
  change D.length*(2*n*m)+(sinkPreserverWithSearchWork G (P.map Prod.fst)).2+
    (sourcePreserverWithSearchWork G (P.map Prod.snd)).2 ≤ hubSearchWorkBound n m D.length
  exact (Nat.add_le_add (Nat.add_le_add_left l _) r).trans_eq (by unfold hubSearchWorkBound bound; ring)

def lateStepSearchWorkBound (n m p : ℕ) : ℕ :=
  2*n*m+hubSearchWorkBound n m p+n*m

private def lateStepWithSearchWork (G : Arcs V) (S : Finset V)
    (st : SteinerPhaseTraces V) (d : V × V) : SteinerPhaseTraces V × ℕ :=
  if d.1 = d.2 then (st,0)
  else
    let n := Fintype.card V
    let m := G.card
    match hitHub G S d with
    | none => (if d ∈ st.thin then st else {st with thin := st.thin++[d]}, 2*n*m)
    | some _ =>
      let hubs := hubPreserverWithSearchWork G S st.hits
      let found := reachInWithArcInspections hubs.1 d.2 n
      (if d.1 ∈ found.1 then st else {st with hits := st.hits++[d]}, 2*n*m+hubs.2+found.2)

private theorem lateStepWithSearchWork_spec {G : Arcs V} (early : EarlySteinerRule G) (S : Finset V)
    (st : SteinerPhaseTraces V) (d : V × V) :
    let out := lateStepWithSearchWork G S st d
    out.1 = steinerPhaseStep early 0 S st d ∧
      out.1.hits.length ≤ st.hits.length+1 ∧ out.1.thin.length ≤ st.thin.length+1 ∧
      (∀ a ∈ out.1.thin, a ∈ st.thin ∨ a = d) ∧
      out.2 ≤ lateStepSearchWorkBound (Fintype.card V) G.card st.hits.length := by
  by_cases self : d.1 = d.2
  · simp [lateStepWithSearchWork, steinerPhaseStep, self, or_iff_not_imp_right]
    aesop
  cases hit : hitHub G S d with
  | none =>
    have bound : 2*Fintype.card V*G.card ≤
        lateStepSearchWorkBound (Fintype.card V) G.card st.hits.length := by
      unfold lateStepSearchWorkBound
      omega
    by_cases seen : d ∈ st.thin
    · simpa [lateStepWithSearchWork, steinerPhaseStep, self, hit, seen] using
        And.intro (fun (a : V × V) (ha : a ∈ st.thin) => Or.inl (b := a = d) ha) bound
    · simp [lateStepWithSearchWork, steinerPhaseStep, self, hit, seen, List.mem_append, bound]
  | some v =>
    let hubs := hubPreserverWithSearchWork G S st.hits
    obtain ⟨same, work⟩ := hubPreserverWithSearchWork_spec G S st.hits
    have arcs : hubs.1.card ≤ G.card := by
      change (hubPreserverWithSearchWork G S st.hits).1.card ≤ _
      rw [same]
      exact card_le_card (hubPreserver_bound G S st.hits).1
    have lim : 2*Fintype.card V*G.card+hubs.2+Fintype.card V*hubs.1.card ≤
        lateStepSearchWorkBound (Fintype.card V) G.card st.hits.length :=
      Nat.add_le_add (Nat.add_le_add_left work _) (Nat.mul_le_mul_left _ arcs)
    change hubs.1 = _ at same
    have reachEq : reachIn hubs.1 d.2 (Fintype.card V) = reaches (hubPreserver G S st.hits) d.2 := by
      rw [same]
      rfl
    by_cases served : d.1 ∈ reaches (hubPreserver G S st.hits) d.2
    · simp only [lateStepWithSearchWork, steinerPhaseStep, self, ite_false, Nat.not_lt_zero,
        hit, ← show hubs = hubPreserverWithSearchWork G S st.hits from rfl,
        reachInWithArcInspections_spec, reachEq, served, ite_true]
      exact ⟨trivial, Nat.le_succ _, Nat.le_succ _, fun _ h => Or.inl h, lim⟩
    · simp only [lateStepWithSearchWork, steinerPhaseStep, self, ite_false, Nat.not_lt_zero,
        hit, ← show hubs = hubPreserverWithSearchWork G S st.hits from rfl,
        reachInWithArcInspections_spec, reachEq, served, ite_false]
      exact ⟨trivial, by simp, Nat.le_succ _, fun _ h => Or.inl h, lim⟩

private def lateTracesWithSearchWorkFrom (G : Arcs V) (S : Finset V) :
    List (V × V) → SteinerPhaseTraces V → SteinerPhaseTraces V × ℕ
  | [], st => (st,0)
  | d::D, st =>
    let step := lateStepWithSearchWork G S st d
    let rest := lateTracesWithSearchWorkFrom G S D step.1
    (rest.1,step.2+rest.2)

private theorem lateTracesWithSearchWorkFrom_spec {G : Arcs V} (early : EarlySteinerRule G)
    (S : Finset V) (D : List (V × V)) (st : SteinerPhaseTraces V) (p : ℕ)
    (hl : st.hits.length+D.length ≤ p) (tl : st.thin.length+D.length ≤ p)
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) (thin : ∀ d ∈ st.thin, Reach G d.1 d.2) :
    let out := lateTracesWithSearchWorkFrom G S D st
    out.1 = D.foldl (steinerPhaseStep early 0 S) st ∧
      out.1.hits.length ≤ p ∧ out.1.thin.length ≤ p ∧
      (∀ d ∈ out.1.thin, Reach G d.1 d.2) ∧
      out.2 ≤ D.length*lateStepSearchWorkBound (Fintype.card V) G.card p := by
  induction D generalizing st with
  | nil => simpa [lateTracesWithSearchWorkFrom] using And.intro hl (And.intro tl thin)
  | cons d D ih =>
    let step := lateStepWithSearchWork G S st d
    let B := lateStepSearchWorkBound (Fintype.card V) G.card p
    obtain ⟨same, hlen, tlen, covers, cost⟩ := lateStepWithSearchWork_spec early S st d
    change step.1 = _ at same
    have safe (a : V × V) (ha : a ∈ step.1.thin) : Reach G a.1 a.2 := by
      rcases covers a ha with earlier | eq
      · exact thin a earlier
      · rw [eq]
        exact feasible d List.mem_cons_self
    have hcap : step.1.hits.length+D.length ≤ p := by
      have l : step.1.hits.length ≤ st.hits.length+1 := hlen
      simp only [List.length_cons] at hl
      omega
    have tcap : step.1.thin.length+D.length ≤ p := by
      have l : step.1.thin.length ≤ st.thin.length+1 := tlen
      simp only [List.length_cons] at tl
      omega
    obtain ⟨result, rh, rt, cover, tail⟩ := ih step.1 hcap tcap
      (fun a ha => feasible a (List.mem_cons_of_mem _ ha)) safe
    have budget : step.2 ≤ B := cost.trans (by
      unfold B lateStepSearchWorkBound
      exact Nat.add_le_add_right (Nat.add_le_add_left (hubSearchWorkBound_mono _ _ (by omega)) _) _)
    refine ⟨result.trans (congrArg (D.foldl (steinerPhaseStep early 0 S)) same), rh, rt, cover, ?_⟩
    change step.2+(lateTracesWithSearchWorkFrom G S D step.1).2 ≤ (D.length+1)*B
    exact (Nat.add_le_add budget tail).trans_eq (by rw [Nat.succ_mul, Nat.add_comm])

private theorem assembledSteiner_zero_eq {G : Arcs V} (early : EarlySteinerRule G) (τ : ℕ)
    (S : Finset V) (sample : ThinSample G) (D : List (V × V)) :
    let st := steinerPhaseTraces early 0 S D
    assembledSteiner early 0 τ S sample D =
      if st.thin.any (fun d => decide (τ < (reachInterval G d).card)) then G
      else hubPreserver G S st.hits ∪
        thinRoundRun G (thinRoundingFactor (Fintype.card V) τ) sample st.thin := by
  dsimp only [assembledSteiner]
  split
  · rfl
  · change early.run (steinerPhaseTraces early 0 S D).early ∪ _ ∪ _ = _
    rw [steinerPhaseTraces_early_empty_at_zero, early.empty, Finset.empty_union]

/-- Charges for arrival classification, the final hub run and thin rounding. -/
def lateSearchWorkBound (n m p : ℕ) : ℕ :=
  p*lateStepSearchWorkBound n m p+p*(2*n*m)+hubSearchWorkBound n m p+
    (p+1)*thinRoundPrefixWorkBound n m p

theorem lateSearchWorkBound_mono (n m : ℕ) : Monotone (lateSearchWorkBound n m) := by
  intro p q le
  unfold lateSearchWorkBound lateStepSearchWorkBound thinRoundPrefixWorkBound hubSearchWorkBound
    liftSearchWorkBound
  gcongr

@[inline] private def lateSteinerWithTraceUsing {X : Type*} (G : Arcs V) (τ m : ℕ) (S : Finset V)
    (D : List (V × V)) (thick : (Arcs V × ℕ) → X)
    (thin : ℕ → (Arcs V × ℕ) → List (V × V) → X) : X :=
  let traces := lateTracesWithSearchWorkFrom G S D ⟨[],[],[]⟩
  let cost := traces.2+traces.1.thin.length*(2*Fintype.card V*m)
  if traces.1.thin.any (fun d => decide (τ < (reachInterval G d).card)) then thick (G,cost)
  else thin cost (hubPreserverWithSearchWork G S traces.1.hits) traces.1.thin

@[inline] private def lateSteinerWithThinWorkUsing (G : Arcs V) (τ m : ℕ) (S : Finset V)
    (roundThin : List (V × V) → (Arcs V × ℕ) × ℕ) (D : List (V × V)) : (Arcs V × ℕ) × ℕ :=
  lateSteinerWithTraceUsing G τ m S D (fun fallback => (fallback,0)) fun cost hubs demands =>
    let thin := roundThin demands
    ((hubs.1 ∪ thin.1.1,cost+hubs.2+thin.1.2),thin.2)

/-- Use a stored thin evaluator together with the same hub trace. -/
def lateSteinerWithSearchWorkUsing (G : Arcs V) (τ m : ℕ) (S : Finset V)
    (roundThin : List (V × V) → Arcs V × ℕ) (D : List (V × V)) : Arcs V × ℕ :=
  lateSteinerWithTraceUsing G τ m S D id fun cost hubs demands =>
    let thin := roundThin demands
    (hubs.1 ∪ thin.1,cost+hubs.2+thin.2)

private theorem lateSteinerWithThinWorkUsing_project (G : Arcs V) (τ m : ℕ) (S : Finset V)
    (roundThin : List (V × V) → (Arcs V × ℕ) × ℕ) (D : List (V × V)) :
    (lateSteinerWithThinWorkUsing G τ m S roundThin D).1 =
      lateSteinerWithSearchWorkUsing G τ m S (fun P => (roundThin P).1) D := by
  dsimp only [lateSteinerWithSearchWorkUsing,lateSteinerWithThinWorkUsing,lateSteinerWithTraceUsing]
  split <;> rfl

/-- Replay the late strategy at cutoff zero. The counters cover hub interval
inspections, the projected path algorithms and thin rounding. -/
def lateSteinerWithSearchWork (G : Arcs V) (τ : ℕ) (S : Finset V)
    (sample : ThinSample G) (D : List (V × V)) : Arcs V × ℕ :=
  lateSteinerWithSearchWorkUsing G τ G.card S
    (fun demands => thinRoundRunWithSearchWork G (thinRoundingFactor (Fintype.card V) τ) sample demands) D

/-- Reuse the supplied thin-threshold rows in all the late fallback checks. -/
def lateSteinerWithStoredThinThresholds (G : Arcs V) (τ m : ℕ) (S : Finset V)
    (rows : Finset ((V × V) × ℕ)) (D : List (V × V)) : Arcs V × ℕ :=
  lateSteinerWithSearchWorkUsing G τ m S
    (fun demands => thinRoundRunFromThresholdRows G m (thinRoundingFactor (Fintype.card V) τ) rows demands) D

theorem lateSteinerWithStoredThinThresholds_eq (G : Arcs V) (τ m : ℕ) (hm : m = G.card)
    (S : Finset V) (sample : ThinSample G) (D : List (V × V)) :
    let prepared := prepareThinThresholdRowsWithSeedReads G m sample
    lateSteinerWithStoredThinThresholds G τ m S prepared.1 D = lateSteinerWithSearchWork G τ S sample D := by
  intro prepared
  let factor := thinRoundingFactor (Fintype.card V) τ
  have same : thinRoundRunFromThresholdRows G m factor prepared.1 = thinRoundRunWithSearchWork G factor sample :=
    funext (fun demands => thinRoundRunFromThresholdRows_eq G m hm factor sample demands)
  change lateSteinerWithSearchWorkUsing G τ m S (thinRoundRunFromThresholdRows G m factor prepared.1) D =
    lateSteinerWithSearchWorkUsing G τ G.card S (thinRoundRunWithSearchWork G factor sample) D
  rw [same,hm]

theorem lateSteinerWithSearchWork_spec {G : Arcs V} (early : EarlySteinerRule G) (τ : ℕ)
    (S : Finset V) (sample : ThinSample G) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := lateSteinerWithSearchWork G τ S sample D
    out.1 = assembledSteiner early 0 τ S sample D ∧
      out.2 ≤ lateSearchWorkBound (Fintype.card V) G.card D.length := by
  let n := Fintype.card V
  let m := G.card
  let p := D.length
  let traces := lateTracesWithSearchWorkFrom G S D ⟨[],[],[]⟩
  obtain ⟨same, hcap, tcap, thins, classification⟩ :=
    lateTracesWithSearchWorkFrom_spec early S D ⟨[],[],[]⟩ p (by simp [p]) (by simp [p])
      feasible (by simp)
  change traces.1 = steinerPhaseTraces early 0 S D at same
  change traces.1.hits.length ≤ p at hcap
  change traces.1.thin.length ≤ p at tcap
  let cost := traces.2+traces.1.thin.length*(2*n*m)
  let hubs := hubPreserverWithSearchWork G S traces.1.hits
  let thin := thinRoundRunWithSearchWork G (thinRoundingFactor n τ) sample traces.1.thin
  let thick := traces.1.thin.any (fun d => decide (τ < (reachInterval G d).card))
  let out : Arcs V × ℕ := if thick then (G,cost) else (hubs.1 ∪ thin.1,cost+hubs.2+thin.2)
  have hb := hubPreserverWithSearchWork_spec G S traces.1.hits
  have tb := thinRoundRunWithSearchWork_spec G (thinRoundingFactor n τ) sample traces.1.thin thins
  have hwork := hb.2.trans (hubSearchWorkBound_mono n m hcap)
  have twork : thin.2 ≤ (p+1)*thinRoundPrefixWorkBound n m p := tb.2.trans (by
    unfold thinRoundPrefixWorkBound
    gcongr)
  have cwork : cost ≤ p*lateStepSearchWorkBound n m p+p*(2*n*m) :=
    Nat.add_le_add classification (Nat.mul_le_mul_right _ tcap)
  change out.1 = assembledSteiner early 0 τ S sample D ∧ out.2 ≤ lateSearchWorkBound n m p
  rw [assembledSteiner_zero_eq, ← same]
  change out.1 = (if thick then G else hubPreserver G S traces.1.hits ∪
    thinRoundRun G (thinRoundingFactor n τ) sample traces.1.thin) ∧ _
  by_cases hit : thick = true
  · simp only [out, hit, ite_true]
    refine ⟨trivial, cwork.trans ?_⟩
    unfold lateSearchWorkBound
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · simp only [out, hit]
    exact ⟨congrArg₂ (· ∪ ·) hb.1 tb.1, Nat.add_le_add (Nat.add_le_add cwork hwork) twork⟩

/-- The stored thin thresholds now feed a single incremental fractional run
per late evaluator call. Keep its extra work separate from the old searches. -/
def lateSteinerWithStreamingThinWork {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (S : Finset (Fin n))
    (rows : ThinThresholdList (Fin n))
    (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  lateSteinerWithThinWorkUsing G τ m S
    (thinRoundRunFromThresholdListWithWordWork G m rows (thinRoundingFactor n τ)) D

theorem lateSteinerWithStreamingThinWork_eq {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (hm : m = G.card)
    (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n))
    (D : List (Fin n × Fin n)) :
    (lateSteinerWithStreamingThinWork G τ m S rows D).1 =
      lateSteinerWithStoredThinThresholds G τ m S rows.val.toFinset D := by
  let round := thinRoundRunFromThresholdListWithWordWork G m rows (thinRoundingFactor n τ)
  have same : (fun P => (round P).1) = thinRoundRunFromThresholdRows G m (thinRoundingFactor n τ) rows.val.toFinset :=
    funext (thinRoundRunFromThresholdListWithWordWork_eq G m hm rows (thinRoundingFactor n τ))
  change (lateSteinerWithThinWorkUsing G τ m S round D).1 = _
  rw [lateSteinerWithThinWorkUsing_project,same]
  simp [lateSteinerWithStoredThinThresholds]

private theorem lateSteinerWithThinWorkUsing_bound {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (τ m : ℕ) (S : Finset (Fin n)) (round : List (Fin n × Fin n) → (Arcs (Fin n) × ℕ) × ℕ)
    (budget : ℕ → ℕ) (mono : Monotone budget)
    (cost : ∀ P, (∀ d ∈ P, Reach G d.1 d.2) → (round P).2 ≤ budget P.length)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (lateSteinerWithThinWorkUsing G τ m S round D).2 ≤ budget D.length := by
  let traces := lateTracesWithSearchWorkFrom G S D ⟨[],[],[]⟩
  obtain ⟨_,_,tcap,thins,_⟩ := lateTracesWithSearchWorkFrom_spec early S D ⟨[],[],[]⟩ D.length
    (by simp) (by simp) feasible (by simp)
  have actual := cost traces.1.thin thins
  dsimp only [lateSteinerWithThinWorkUsing,lateSteinerWithTraceUsing]
  split
  · exact Nat.zero_le _
  · exact actual.trans (mono tcap)

theorem lateSteinerWithStreamingThinWork_bound {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (τ m : ℕ) (hm : m = G.card) (S : Finset (Fin n))
    (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (lateSteinerWithStreamingThinWork G τ m S rows D).2 ≤ steinerStreamingThinWorkBound n m D.length := by
  apply lateSteinerWithThinWorkUsing_bound early τ m S _ (steinerStreamingThinWorkBound n m) _ _ D feasible
  · intro a b short
    unfold steinerStreamingThinWorkBound
    gcongr
  · exact thinRoundRunFromThresholdListWithWordWork_bound G m hm rows edges count (thinRoundingFactor n τ)

/-- Preserve hub processing and add the indexed separator to the thin branch. -/
def lateSteinerWithThinSeparatorWork {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (S : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  lateSteinerWithThinWorkUsing G τ m S
    (thinRoundRunFromThresholdListWithSeparatorWork G m rows (thinRoundingFactor n τ)) D

theorem lateSteinerWithThinSeparatorWork_eq {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (hm : m = G.card)
    (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) :
    (lateSteinerWithThinSeparatorWork G τ m S rows D).1 =
      lateSteinerWithStoredThinThresholds G τ m S rows.val.toFinset D := by
  let round := thinRoundRunFromThresholdListWithSeparatorWork G m rows (thinRoundingFactor n τ)
  have same : (fun P => (round P).1) = thinRoundRunFromThresholdRows G m (thinRoundingFactor n τ) rows.val.toFinset :=
    funext (thinRoundRunFromThresholdListWithSeparatorWork_eq G m hm rows (thinRoundingFactor n τ))
  change (lateSteinerWithThinWorkUsing G τ m S round D).1 = _
  rw [lateSteinerWithThinWorkUsing_project,same]
  simp [lateSteinerWithStoredThinThresholds]

theorem lateSteinerWithThinSeparatorWork_bound {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (τ m : ℕ) (hm : m = G.card) (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (lateSteinerWithThinSeparatorWork G τ m S rows D).2 ≤ steinerThinSeparatorWorkBound n m D.length := by
  apply lateSteinerWithThinWorkUsing_bound early τ m S _ (steinerThinSeparatorWorkBound n m) _ _ D feasible
  · intro a b short
    unfold steinerThinSeparatorWorkBound steinerStreamingThinWorkBound
    gcongr
  · exact thinRoundRunFromThresholdListWithSeparatorWork_bound G m hm rows edges count (thinRoundingFactor n τ)

/-- Keep the hub phase and use stored capacities and indexed residual scans in the thin branch. -/
def lateSteinerWithIndexedThinTablesWork {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (S : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  lateSteinerWithThinWorkUsing G τ m S
    (thinRoundRunFromThresholdListWithIndexedTablesWork G m rows (thinRoundingFactor n τ)) D

theorem lateSteinerWithIndexedThinTablesWork_eq {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (hm : m = G.card)
    (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) :
    (lateSteinerWithIndexedThinTablesWork G τ m S rows D).1 =
      lateSteinerWithStoredThinThresholds G τ m S rows.val.toFinset D := by
  let round := thinRoundRunFromThresholdListWithIndexedTablesWork G m rows (thinRoundingFactor n τ)
  have same : (fun P => (round P).1) = thinRoundRunFromThresholdRows G m (thinRoundingFactor n τ) rows.val.toFinset :=
    funext (thinRoundRunFromThresholdListWithIndexedTablesWork_eq G m hm rows (thinRoundingFactor n τ))
  change (lateSteinerWithThinWorkUsing G τ m S round D).1 = _
  rw [lateSteinerWithThinWorkUsing_project,same]
  simp [lateSteinerWithStoredThinThresholds]

theorem lateSteinerWithIndexedThinTablesWork_bound {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (τ m : ℕ) (hm : m = G.card) (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (lateSteinerWithIndexedThinTablesWork G τ m S rows D).2 ≤ steinerThinIndexedTablesWorkBound n m D.length := by
  apply lateSteinerWithThinWorkUsing_bound early τ m S _ (steinerThinIndexedTablesWorkBound n m) _ _ D feasible
  · intro a b short
    unfold steinerThinIndexedTablesWorkBound steinerStreamingThinWorkBound
    gcongr
  · exact thinRoundRunFromThresholdListWithIndexedTablesWork_bound G m hm rows edges count (thinRoundingFactor n τ)

/-- Evaluate the late phase with metered residual routes. -/
def lateSteinerWithThinResidualRouteWork {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (S : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  lateSteinerWithThinWorkUsing G τ m S
    (thinRoundRunFromThresholdListWithResidualRouteWork G m rows (thinRoundingFactor n τ)) D

theorem lateSteinerWithThinResidualRouteWork_eq {n : ℕ} (G : Arcs (Fin n)) (τ m : ℕ) (hm : m = G.card)
    (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) :
    (lateSteinerWithThinResidualRouteWork G τ m S rows D).1 =
      lateSteinerWithStoredThinThresholds G τ m S rows.val.toFinset D := by
  let round := thinRoundRunFromThresholdListWithResidualRouteWork G m rows (thinRoundingFactor n τ)
  have same : (fun P => (round P).1) = thinRoundRunFromThresholdRows G m (thinRoundingFactor n τ) rows.val.toFinset :=
    funext (thinRoundRunFromThresholdListWithResidualRouteWork_eq G m hm rows (thinRoundingFactor n τ))
  change (lateSteinerWithThinWorkUsing G τ m S round D).1 = _
  rw [lateSteinerWithThinWorkUsing_project,same]
  simp [lateSteinerWithStoredThinThresholds]

theorem lateSteinerWithThinResidualRouteWork_bound {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (τ m : ℕ) (hm : m = G.card) (S : Finset (Fin n)) (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (lateSteinerWithThinResidualRouteWork G τ m S rows D).2 ≤ steinerThinResidualRouteWorkBound n m D.length := by
  apply lateSteinerWithThinWorkUsing_bound early τ m S _ (steinerThinResidualRouteWorkBound n m) _ _ D feasible
  · intro a b short
    unfold steinerThinResidualRouteWorkBound steinerStreamingThinWorkBound
    gcongr
  · exact thinRoundRunFromThresholdListWithResidualRouteWork_bound G m hm rows edges count (thinRoundingFactor n τ)

end OnlineReachabilityPreservers
