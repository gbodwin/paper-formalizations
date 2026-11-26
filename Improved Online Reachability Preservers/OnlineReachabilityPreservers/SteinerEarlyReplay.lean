import OnlineReachabilityPreservers.AlgorithmSearchWork
import OnlineReachabilityPreservers.SeparatorWork
import OnlineReachabilityPreservers.SteinerEarlyRound
import OnlineReachabilityPreservers.SteinerPhaseUnionWork

/-! Compose weighted separation, route expansion and failure tests across early prefixes. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Bound the original-graph route searches for one metric link. -/
def labelledRouteSearchBound (n m : ℕ) : ℕ :=
  m*(2*((n+1)*n*m))+n*m+2*n^2

private def labelledLinkWorkRow {A : Type*} (G : Arcs V) (label : A → V) :
    (A × A) ↪ (A × A) × Option (List (V × V)) × ℕ × ℕ :=
  ⟨fun e => (e, routePathWithSearchWork G (label e.1) (label e.2)), fun _ _ h => congrArg Prod.fst h⟩

/-- Expand each selected link once and count its ordinary route searches. -/
def expandLabelledLinksWithSearchWork {A : Type*}
    (G : Arcs V) (label : A → V) (links : Arcs A) : Arcs V × ℕ :=
  let rows := links.map (labelledLinkWorkRow G label)
  (rows.biUnion (fun r => pathArcs r.2.1), ∑ r ∈ rows, (r.2.2.1+r.2.2.2))

theorem expandLabelledLinksWithSearchWork_spec {A : Type*}
    (G : Arcs V) (label : A → V) (links : Arcs A) :
    let out := expandLabelledLinksWithSearchWork G label links
    out.1 = expandLabelledLinks G label links ∧
      out.2 ≤ links.card*labelledRouteSearchBound (Fintype.card V) G.card := by
  let row := labelledLinkWorkRow G label
  let B := labelledRouteSearchBound (Fintype.card V) G.card
  have same (e : A × A) : (row e).2.1 = routePath G (label e.1) (label e.2) :=
    (routePathWithSearchWork_spec G (label e.1) (label e.2)).1
  refine ⟨?_, ?_⟩
  · ext e
    change e ∈ (links.map row).biUnion (fun x => pathArcs x.2.1) ↔ e ∈ expandLabelledLinks G label links
    unfold expandLabelledLinks
    constructor
    · intro he
      obtain ⟨r, hr, used⟩ := mem_biUnion.mp he
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
      exact mem_biUnion.mpr ⟨a, ha, (same a) ▸ used⟩
    · intro he
      obtain ⟨a, ha, used⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr ⟨row a, mem_map_of_mem _ ha, (same a).symm ▸ used⟩
  · change (∑ r ∈ links.map row, (r.2.2.1+r.2.2.2)) ≤ links.card*B
    rw [sum_map]
    calc
      _ ≤ ∑ _ ∈ links, B := by
        apply sum_le_sum
        intro a _
        obtain ⟨_, arc, tests⟩ := routePathWithSearchWork_spec G (label a.1) (label a.2)
        exact Nat.add_le_add arc tests
      _ = _ := by simp

/-- Upper budget for the measured work at one early prefix. The forest
rounding arithmetic and formation of its template are outside this count. -/
def earlyPrefixSearchWorkBound (n m forest network p : ℕ) : ℕ :=
  let B := max 1 (n*forest^2)
  p*(((B+1)*B+1)*weightedSeparatorWorkBound network (network^2) B) +
    forest^2*labelledRouteSearchBound n m+n*m

/-- Include each early prefix and the possible final route expansion. -/
def earlySearchWorkBound (n m forest network p : ℕ) : ℕ :=
  (p+1)*earlyPrefixSearchWorkBound n m forest network p+forest^2*labelledRouteSearchBound n m

theorem earlySearchWorkBound_mono (n m : ℕ) {F F' N N' p p' : ℕ}
    (forest : F ≤ F') (network : N ≤ N') (len : p ≤ p') :
    earlySearchWorkBound n m F N p ≤ earlySearchWorkBound n m F' N' p' := by
  unfold earlySearchWorkBound earlyPrefixSearchWorkBound weightedSeparatorWorkBound residualStepWorkBound
  dsimp only
  gcongr

/-- The ordinary weighted prefix and its metric purchases, before expansion. -/
def earlyMetricWithSearchWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ :=
  let frac := forestFractionalRunWithSearchWork G height P
  (roundedForestTrials G frac.1.1 (forestScale G height) (earlyTrialCount V height) sample,frac.2)

private def earlyPrefixWorkEntry (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ)
    (P : List (V × V)) : List (V × V) × Arcs (HeightForestVertex V height) × Bool × ℕ :=
  match P.getLast? with
  | none => (P, ∅, false, 0)
  | some d =>
    let bought := metric P
    let expanded := expandLabelledLinksWithSearchWork G heightForestLabel bought.1
    let check := reachInWithArcInspections expanded.1 d.2 (Fintype.card V)
    (P, bought.1, decide (d.1 ∉ check.1), bought.2+expanded.2+check.2)

private theorem earlyPrefixWorkEntry_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (P : List (V × V)) :
    let row := earlyPrefixWorkEntry G height (earlyMetricWithSearchWork G height sample) P
    row.2.1 = (if P = [] then ∅ else earlyMetricAt G height P sample) ∧
      (row.2.2.1 = true ↔ earlyRoundMiss G height P sample) ∧
      row.2.2.2 ≤ earlyPrefixSearchWorkBound (Fintype.card V) G.card
        (Fintype.card (HeightForestVertex V height)) (Fintype.card (ForestNetworkVertex V height)) P.length := by
  cases h : P.getLast? with
  | none =>
    have empty : P = [] := List.getLast?_eq_none_iff.mp h
    subst P
    simp [earlyPrefixWorkEntry, earlyRoundMiss]
  | some d =>
    have notEmpty : P ≠ [] := fun eq => by simp [eq] at h
    let frac := forestFractionalRunWithSearchWork G height P
    let metric := roundedForestTrials G frac.1.1 (forestScale G height) (earlyTrialCount V height) sample
    let expanded := expandLabelledLinksWithSearchWork G heightForestLabel metric
    obtain ⟨charges, work⟩ := forestFractionalRunWithSearchWork_spec G height P
    have metricEq : metric = earlyMetricAt G height P sample := by
      unfold metric earlyMetricAt
      rw [show frac.1 = forestFractionalRun G height P from charges]
    obtain ⟨arcs, routes⟩ := expandLabelledLinksWithSearchWork_spec G heightForestLabel metric
    have arcBound : expanded.1.card ≤ G.card := by
      change (expandLabelledLinksWithSearchWork G heightForestLabel metric).1.card ≤ _
      rw [arcs]
      exact card_le_card (expandLabelledLinks_sub _ _ _)
    have metricBound : metric.card ≤ Fintype.card (HeightForestVertex V height)^2 := by
      simpa only [Fintype.card_prod, pow_two] using card_le_univ metric
    simp only [earlyPrefixWorkEntry, earlyMetricWithSearchWork, earlyRoundMiss, h, notEmpty, ite_false,
      reachInWithArcInspections_spec, decide_eq_true_eq]
    refine ⟨metricEq, ?_, ?_⟩
    · rw [arcs, metricEq]
      rfl
    · exact Nat.add_le_add (Nat.add_le_add work (routes.trans (Nat.mul_le_mul_right _ metricBound)))
        (Nat.mul_le_mul_left _ arcBound)

private def earlyPrefixWorkRow (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ) :
    List (V × V) ↪ List (V × V) × Arcs (HeightForestVertex V height) × Bool × ℕ where
  toFun := earlyPrefixWorkEntry G height metric
  inj' := by
    have key (P : List (V × V)) : (earlyPrefixWorkEntry G height metric P).1 = P := by
      unfold earlyPrefixWorkEntry
      split <;> rfl
    intro P Q equal
    exact (key P).symm.trans ((congrArg Prod.fst equal).trans (key Q))

/-- Replay prefix misses and the final purchases from a given metric evaluator. -/
def earlyRoundedGraphWithSearchWorkFromMetric (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ)
    (D : List (V × V)) : Arcs V × ℕ :=
  let rows := D.inits.toFinset.map (earlyPrefixWorkRow G height metric)
  let work := ∑ r ∈ rows, r.2.2.2
  if (rows.filter fun r => r.2.2.1 = true).Nonempty then (G, work)
  else
    let bought := rows.biUnion (fun r => r.2.1)
    let expanded := expandLabelledLinksWithSearchWork G heightForestLabel bought
    (expanded.1, work+expanded.2)

/-- Run the early fallback test and union purchases using the cached
result of each fractional prefix computation. -/
def earlyRoundedGraphWithSearchWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (D : List (V × V)) : Arcs V × ℕ :=
  earlyRoundedGraphWithSearchWorkFromMetric G height (earlyMetricWithSearchWork G height sample) D

theorem earlyRoundedGraphWithSearchWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (D : List (V × V)) :
    let F := Fintype.card (HeightForestVertex V height)
    let N := Fintype.card (ForestNetworkVertex V height)
    let out := earlyRoundedGraphWithSearchWork G height sample D
    out.1 = earlyRoundedGraph G height D sample ∧
      out.2 ≤ earlySearchWorkBound (Fintype.card V) G.card F N D.length := by
  let rows := D.inits.toFinset.map (earlyPrefixWorkRow G height (earlyMetricWithSearchWork G height sample))
  let B := earlyPrefixSearchWorkBound (Fintype.card V) G.card
    (Fintype.card (HeightForestVertex V height)) (Fintype.card (ForestNetworkVertex V height)) D.length
  have same : (rows.filter fun r => r.2.2.1 = true).Nonempty ↔ earlyRoundFallback G height D sample := by
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨member, mark⟩ := mem_filter.mp hr
      obtain ⟨P, hp, rfl⟩ := mem_map.mp member
      exact ⟨P, hp, (earlyPrefixWorkEntry_spec G height sample P).2.1.mp mark⟩
    · rintro ⟨P, hp, miss⟩
      exact ⟨_, mem_filter.mpr ⟨mem_map_of_mem _ hp, (earlyPrefixWorkEntry_spec G height sample P).2.1.mpr miss⟩⟩
  have bought : rows.biUnion (fun r => r.2.1) = earlyMetricPurchases G height D sample := by
    ext e
    unfold earlyMetricPurchases
    constructor
    · intro he
      obtain ⟨r, hr, inside⟩ := mem_biUnion.mp he
      obtain ⟨P, hp, rfl⟩ := mem_map.mp hr
      exact mem_biUnion.mpr ⟨P, hp, (earlyPrefixWorkEntry_spec G height sample P).1 ▸ inside⟩
    · intro he
      obtain ⟨P, hp, inside⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr ⟨_, mem_map_of_mem _ hp,
        (earlyPrefixWorkEntry_spec G height sample P).1.symm ▸ inside⟩
  have work : (∑ r ∈ rows, r.2.2.2) ≤ (D.length+1)*B := by
    calc
      _ ≤ ∑ _ ∈ rows, B := by
        apply sum_le_sum
        intro r hr
        obtain ⟨P, hp, rfl⟩ := mem_map.mp hr
        have pref := (List.mem_inits _ _).mp (List.mem_toFinset.mp hp)
        exact (earlyPrefixWorkEntry_spec G height sample P).2.2.trans (by
          have smaller := pref.length_le
          dsimp only [B, earlyPrefixSearchWorkBound]
          gcongr)
      _ = rows.card*B := by simp
      _ ≤ (D.length+1)*B := by
        have length : rows.card ≤ D.inits.length := (Finset.card_map (earlyPrefixWorkRow G height (earlyMetricWithSearchWork G height sample))).le.trans (List.toFinset_card_le _)
        rw [List.length_inits] at length
        exact Nat.mul_le_mul_right _ length
  let cost := ∑ r ∈ rows, r.2.2.2
  let plan := expandLabelledLinksWithSearchWork G heightForestLabel (rows.biUnion fun r => r.2.1)
  let out : Arcs V × ℕ := if (rows.filter fun r => r.2.2.1 = true).Nonempty then
    (G,cost) else (plan.1,cost+plan.2)
  change out.1 = earlyRoundedGraph G height D sample ∧ out.2 ≤ (D.length+1)*B+
    Fintype.card (HeightForestVertex V height)^2*labelledRouteSearchBound (Fintype.card V) G.card
  by_cases fail : earlyRoundFallback G height D sample
  · simp only [out, earlyRoundedGraph, ite_eq_left (same.mpr fail), ite_eq_left fail]
    exact ⟨trivial, work.trans (Nat.le_add_right _ _)⟩
  · simp only [out, earlyRoundedGraph, ite_eq_right ((not_congr same).mpr fail), ite_eq_right fail]
    obtain ⟨arcs, expand⟩ := expandLabelledLinksWithSearchWork_spec G heightForestLabel (rows.biUnion fun r => r.2.1)
    refine ⟨arcs.trans ?_, Nat.add_le_add work (expand.trans (Nat.mul_le_mul_right _ ?_))⟩
    · rw [bought]
      rfl
    · simpa only [Fintype.card_prod, pow_two] using card_le_univ (rows.biUnion fun r => r.2.1)

/-- Charge an additional per-metric cost without changing any graph or miss
flag. The prefix rows share each metric result between all uses. -/
theorem earlyRoundedGraphWithSearchWorkFromMetric_compareOnPrefixes (G : Arcs V) (height : ℕ)
    (original updated : List (V × V) → Arcs (HeightForestVertex V height) × ℕ) (K : ℕ)
    (D : List (V × V))
    (metric : ∀ P ∈ D.inits, (updated P).1 = (original P).1 ∧ (updated P).2 ≤ (original P).2+K) :
    let out := earlyRoundedGraphWithSearchWorkFromMetric G height updated D
    let old := earlyRoundedGraphWithSearchWorkFromMetric G height original D
    out.1 = old.1 ∧ out.2 ≤ old.2+(D.length+1)*K := by
  let A := D.inits.toFinset
  let readOld := earlyPrefixWorkRow G height original
  let readNew := earlyPrefixWorkRow G height updated
  let oldRows := A.map readOld
  let newRows := A.map readNew
  have row (P : List (V × V)) (present : P ∈ A) :
      let prior := readOld P
      let next := readNew P
      next.2.1 = prior.2.1 ∧ next.2.2.1 = prior.2.2.1 ∧ next.2.2.2 ≤ prior.2.2.2+K := by
    have ⟨graph, cost⟩ := metric P (List.mem_toFinset.mp present)
    change (earlyPrefixWorkEntry G height updated P).2.1 = (earlyPrefixWorkEntry G height original P).2.1 ∧
      (earlyPrefixWorkEntry G height updated P).2.2.1 = (earlyPrefixWorkEntry G height original P).2.2.1 ∧
      (earlyPrefixWorkEntry G height updated P).2.2.2 ≤ (earlyPrefixWorkEntry G height original P).2.2.2+K
    cases ending : P.getLast? with
    | none => simp [earlyPrefixWorkEntry, ending]
    | some d =>
      simp only [earlyPrefixWorkEntry, ending, graph, true_and]
      omega
  have failure : (newRows.filter fun r => r.2.2.1 = true).Nonempty ↔
      (oldRows.filter fun r => r.2.2.1 = true).Nonempty := by
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨seen,miss⟩ := mem_filter.mp hr
      obtain ⟨P,hP,rfl⟩ := mem_map.mp seen
      exact ⟨readOld P, mem_filter.mpr ⟨mem_map_of_mem _ hP, (row P hP).2.1 ▸ miss⟩⟩
    · rintro ⟨r,hr⟩
      obtain ⟨seen,miss⟩ := mem_filter.mp hr
      obtain ⟨P,hP,rfl⟩ := mem_map.mp seen
      exact ⟨readNew P, mem_filter.mpr ⟨mem_map_of_mem _ hP, (row P hP).2.1.symm ▸ miss⟩⟩
  have purchases : newRows.biUnion (fun r => r.2.1) = oldRows.biUnion (fun r => r.2.1) := by
    ext a
    constructor
    · intro bought
      obtain ⟨r,seen,used⟩ := mem_biUnion.mp bought
      obtain ⟨P,hP,rfl⟩ := mem_map.mp seen
      exact mem_biUnion.mpr ⟨readOld P,mem_map_of_mem _ hP,(row P hP).1 ▸ used⟩
    · intro bought
      obtain ⟨r,seen,used⟩ := mem_biUnion.mp bought
      obtain ⟨P,hP,rfl⟩ := mem_map.mp seen
      exact mem_biUnion.mpr ⟨readNew P,mem_map_of_mem _ hP,(row P hP).1.symm ▸ used⟩
  let oldSum := ∑ r ∈ oldRows, r.2.2.2
  let newSum := ∑ r ∈ newRows, r.2.2.2
  have summed : newSum ≤ oldSum+(D.length+1)*K := by
    change (∑ r ∈ A.map readNew, r.2.2.2) ≤ (∑ r ∈ A.map readOld, r.2.2.2)+(D.length+1)*K
    rw [sum_map, sum_map]
    calc
      _ ≤ ∑ P ∈ A, ((readOld P).2.2.2+K) := sum_le_sum fun P hP => (row P hP).2.2
      _ = (∑ P ∈ A, (readOld P).2.2.2)+A.card*K := by rw [sum_add_distrib]; simp
      _ ≤ _ := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_right
        exact (List.toFinset_card_le D.inits).trans_eq (List.length_inits D)
  let final := expandLabelledLinksWithSearchWork G heightForestLabel (oldRows.biUnion fun r => r.2.1)
  let outNew : Arcs V × ℕ := if (newRows.filter fun r => r.2.2.1 = true).Nonempty then
    (G,newSum) else
      let exp := expandLabelledLinksWithSearchWork G heightForestLabel (newRows.biUnion fun r => r.2.1)
      (exp.1,newSum+exp.2)
  let outOld : Arcs V × ℕ := if (oldRows.filter fun r => r.2.2.1 = true).Nonempty then
    (G,oldSum) else (final.1,oldSum+final.2)
  change outNew.1 = outOld.1 ∧ outNew.2 ≤ outOld.2+(D.length+1)*K
  by_cases failed : (oldRows.filter fun r => r.2.2.1 = true).Nonempty
  · simp only [outNew, outOld, (failure.mpr failed), failed, ite_true, true_and]
    exact summed
  · simp only [outNew, outOld, (not_congr failure).mpr failed, failed, ite_false, purchases, final, true_and]
    omega

theorem earlyRoundedGraphWithSearchWorkFromMetric_compare (G : Arcs V) (height : ℕ)
    (original updated : List (V × V) → Arcs (HeightForestVertex V height) × ℕ) (K : ℕ)
    (metric : ∀ P, (updated P).1 = (original P).1 ∧ (updated P).2 ≤ (original P).2+K)
    (D : List (V × V)) :
    let out := earlyRoundedGraphWithSearchWorkFromMetric G height updated D
    let old := earlyRoundedGraphWithSearchWorkFromMetric G height original D
    out.1 = old.1 ∧ out.2 ≤ old.2+(D.length+1)*K :=
  earlyRoundedGraphWithSearchWorkFromMetric_compareOnPrefixes G height original updated K D (fun P _ => metric P)

private def earlyPrefixSeedReadRow (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ) :
    List (V × V) ↪ (List (V × V) × Arcs (HeightForestVertex V height) × Bool × ℕ) × ℕ where
  toFun P :=
    let bought := if P.isEmpty then (∅,0,0) else metric P
    (earlyPrefixWorkEntry G height (fun _ => (bought.1,bought.2.1)) P,bought.2.2)
  inj' := by
    have key (M : List (V × V) → Arcs (HeightForestVertex V height) × ℕ) (P : List (V × V)) :
        (earlyPrefixWorkEntry G height M P).1 = P := by
      unfold earlyPrefixWorkEntry
      split <;> rfl
    intro P Q same
    exact (key _ P).symm.trans ((congrArg (fun x => x.1.1) same).trans (key _ Q))

private theorem earlyPrefixSeedReadRow_spec (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (B : ℕ) (P : List (V × V)) (bound : (metric P).2.2 ≤ B) :
    let row := earlyPrefixSeedReadRow G height metric P
    row.1 = earlyPrefixWorkRow G height (fun Q => ((metric Q).1,(metric Q).2.1)) P ∧ row.2 ≤ B := by
  cases P with
  | nil => exact ⟨rfl,Nat.zero_le B⟩
  | cons d tail =>
    refine ⟨?_,bound⟩
    change earlyPrefixWorkEntry G height (fun _ => ((metric (d :: tail)).1,(metric (d :: tail)).2.1))
      (d :: tail) = earlyPrefixWorkEntry G height (fun Q => ((metric Q).1,(metric Q).2.1)) (d :: tail)
    unfold earlyPrefixWorkEntry
    split <;> rfl

/-- Evaluate every needed metric prefix once, retaining its seed reads
alongside the existing search and weight-read count. -/
def earlyRoundedGraphWithSeedReadsFromMetric (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (D : List (V × V)) : Arcs V × ℕ × ℕ :=
  let rows := D.inits.toFinset.map (earlyPrefixSeedReadRow G height metric)
  let work := ∑ r ∈ rows, r.1.2.2.2
  let reads := ∑ r ∈ rows, r.2
  if (rows.filter fun r => r.1.2.2.1 = true).Nonempty then (G,work,reads)
  else
    let bought := rows.biUnion (fun r => r.1.2.1)
    let expanded := expandLabelledLinksWithSearchWork G heightForestLabel bought
    (expanded.1,work+expanded.2,reads)

theorem earlyRoundedGraphWithSeedReadsFromMetric_spec (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (D : List (V × V)) (B : ℕ) (bound : ∀ P ∈ D.inits, (metric P).2.2 ≤ B) :
    let out := earlyRoundedGraphWithSeedReadsFromMetric G height metric D
    (out.1,out.2.1) = earlyRoundedGraphWithSearchWorkFromMetric G height
      (fun P => ((metric P).1,(metric P).2.1)) D ∧ out.2.2 ≤ (D.length+1)*B := by
  let source := D.inits.toFinset
  let row := earlyPrefixSeedReadRow G height metric
  let old := earlyPrefixWorkRow G height (fun P => ((metric P).1,(metric P).2.1))
  let rows := source.map row
  let prior := source.map old
  have each (P : List (V × V)) (mem : P ∈ source) :=
    earlyPrefixSeedReadRow_spec G height metric B P (bound P (List.mem_toFinset.mp mem))
  have reads : (∑ r ∈ rows, r.2) ≤ (D.length+1)*B := by
    dsimp only [rows]
    rw [sum_map]
    calc
      _ ≤ ∑ _ ∈ source, B := sum_le_sum fun P mem => (each P mem).2
      _ = source.card*B := by simp
      _ ≤ _ := Nat.mul_le_mul_right B (by simpa only [source,List.length_inits] using D.inits.toFinset_card_le)
  have work : (∑ r ∈ rows, r.1.2.2.2) = ∑ r ∈ prior, r.2.2.2 := by
    dsimp only [rows,prior]
    rw [sum_map,sum_map]
    exact sum_congr rfl fun P mem => congrArg (fun x => x.2.2.2) (each P mem).1
  have misses : (rows.filter fun r => r.1.2.2.1 = true).Nonempty ↔
      (prior.filter fun r => r.2.2.1 = true).Nonempty := by
    constructor
    · rintro ⟨r,mem⟩
      obtain ⟨present,miss⟩ := mem_filter.mp mem
      obtain ⟨P,inside,rfl⟩ := mem_map.mp present
      exact ⟨old P,mem_filter.mpr ⟨mem_map_of_mem _ inside,(each P inside).1 ▸ miss⟩⟩
    · rintro ⟨r,mem⟩
      obtain ⟨present,miss⟩ := mem_filter.mp mem
      obtain ⟨P,inside,rfl⟩ := mem_map.mp present
      exact ⟨row P,mem_filter.mpr ⟨mem_map_of_mem _ inside,(each P inside).1.symm ▸ miss⟩⟩
  have bought : rows.biUnion (fun r => r.1.2.1) = prior.biUnion (fun r => r.2.1) := by
    ext e
    constructor
    · intro mem
      obtain ⟨r,present,contains⟩ := mem_biUnion.mp mem
      obtain ⟨P,inside,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨old P,mem_map_of_mem _ inside,(each P inside).1 ▸ contains⟩
    · intro mem
      obtain ⟨r,present,contains⟩ := mem_biUnion.mp mem
      obtain ⟨P,inside,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨row P,mem_map_of_mem _ inside,(each P inside).1.symm ▸ contains⟩
  dsimp only [earlyRoundedGraphWithSeedReadsFromMetric,earlyRoundedGraphWithSearchWorkFromMetric]
  by_cases fail : (prior.filter fun r => r.2.2.1 = true).Nonempty
  · have same := misses.mpr fail
    rw [ite_eq_left same,ite_eq_left fail,work]
    exact ⟨rfl,reads⟩
  · have same := mt misses.mp fail
    rw [ite_eq_right same,ite_eq_right fail,bought,work]
    exact ⟨rfl,reads⟩


/-- Compare early metric callbacks whose graphs agree and whose ordinary
search count can only decrease. Bound the new separate tally on prefixes. -/
theorem earlyRoundedGraphWithSeedReadsFromMetric_compare (G : Arcs V) (height : ℕ)
    (next prior : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (D : List (V × V)) (B : ℕ)
    (compare : ∀ P ∈ D.inits, (next P).1 = (prior P).1 ∧ (next P).2.1 ≤ (prior P).2.1)
    (bound : ∀ P ∈ D.inits, (next P).2.2 ≤ B) :
    let out := earlyRoundedGraphWithSeedReadsFromMetric G height next D
    let old := earlyRoundedGraphWithSeedReadsFromMetric G height prior D
    out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧ out.2.2 ≤ (D.length+1)*B := by
  let priorCap := ∑ P ∈ D.inits.toFinset, (prior P).2.2
  have priorBound (P : List (V × V)) (on : P ∈ D.inits) : (prior P).2.2 ≤ priorCap :=
    single_le_sum (f := fun Q => (prior Q).2.2) (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr on)
  obtain ⟨newMatch, newWork⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G height next D B bound
  obtain ⟨oldMatch, _⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G height prior D priorCap priorBound
  have same := earlyRoundedGraphWithSearchWorkFromMetric_compareOnPrefixes G height
    (fun P => ((prior P).1,(prior P).2.1)) (fun P => ((next P).1,(next P).2.1)) 0 D
    (fun P on => ⟨(compare P on).1, by simpa only [Nat.add_zero] using (compare P on).2⟩)
  refine ⟨(congrArg Prod.fst newMatch).trans (same.1.trans (congrArg Prod.fst oldMatch).symm), ?_, newWork⟩
  refine (congrArg Prod.snd newMatch).le.trans ((?_ : _ ≤ _).trans (congrArg Prod.snd oldMatch).symm.le)
  simpa only [Nat.mul_zero, Nat.add_zero] using same.2

private structure ExpandedMetricRow (V : Type*) (height : ℕ) where
  requests : List (V × V)
  bought : Arcs (HeightForestVertex V height)
  failed : Bool
  searches : ℕ
  work : ℕ

private abbrev EarlyExpansionValidation (V : Type*) := Arcs V → V × V → Bool × ℕ × ℕ

private def earlyExpansionArcInspections (n : ℕ) (H : Arcs V) (d : V × V) : Bool × ℕ × ℕ :=
  let checked := reachInWithArcInspections H d.2 n
  (decide (d.1 ∉ checked.1),checked.2,0)

@[inline] private def earlyExpandedMetricValueWithLast (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V)
    (P : List (V × V)) (last : Option (V × V)) : ExpandedMetricRow V height :=
  match last with
  | none => ⟨P,∅,false,0,8⟩
  | some d =>
    let bought := metric P
    let expanded := expand bought.1
    let check := validate expanded.1 d
    ⟨P,bought.1,check.1,bought.2.1+check.2.1,bought.2.2+expanded.2+check.2.2+8⟩

@[inline] private def earlyExpandedMetricValue (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V)
    (P : List (V × V)) : ExpandedMetricRow V height :=
  earlyExpandedMetricValueWithLast height metric expand validate P P.getLast?

private def earlyExpandedMetricRow (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) :
    List (V × V) ↪ ExpandedMetricRow V height where
  toFun := earlyExpandedMetricValue height metric expand validate
  inj' := by
    have key (P : List (V × V)) : (earlyExpandedMetricValue height metric expand validate P).requests = P := by
      unfold earlyExpandedMetricValue earlyExpandedMetricValueWithLast
      split <;> rfl
    intro P Q same
    exact (key P).symm.trans ((congrArg ExpandedMetricRow.requests same).trans (key Q))

omit [LinearOrder V] [Fintype V] in
private theorem earlyExpandedMetricRow_apply (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) (P : List (V × V)) :
    earlyExpandedMetricRow height metric expand validate P = earlyExpandedMetricValue height metric expand validate P := rfl

/-- Use the supplied expansion and validation routines at each early
prefix, then expand the final bought union when all checks succeed. -/
def earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) (D : List (V × V)) : Arcs V × ℕ × ℕ :=
  let rows := D.inits.toFinset.map (earlyExpandedMetricRow height metric expand validate)
  let searches := ∑ r ∈ rows, r.searches
  let work := ∑ r ∈ rows, r.work
  if (rows.filter fun r => r.failed = true).Nonempty then (G,searches,work+6)
  else
    let expanded := expand (rows.biUnion ExpandedMetricRow.bought)
    (expanded.1,searches,work+expanded.2+6)

/-- Use the metered expansion when validating each early prefix and when
returning the final union of the bought links. -/
def earlyRoundedGraphWithSeedReadsAndExpansionFromMetric (G : Arcs V) (n height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (D : List (V × V)) : Arcs V × ℕ × ℕ :=
  earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric G height metric expand (earlyExpansionArcInspections n) D

private theorem earlyExpandedMetricRow_compare (G : Arcs V) (n height : ℕ) (size : n = Fintype.card V)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) (P : List (V × V)) (B E C : ℕ) (metricCap : (metric P).2.2 ≤ B)
    (expansion : (expand (metric P).1).1 = (expandLabelledLinksWithSearchWork G heightForestLabel (metric P).1).1 ∧
      (expand (metric P).1).2 ≤ E)
    (validation : ∀ d,
      let out := validate (expand (metric P).1).1 d
      let old := reachInWithArcInspections (expand (metric P).1).1 d.2 n
      out.1 = decide (d.1 ∉ old.1) ∧ out.2.1 ≤ old.2 ∧ out.2.2 ≤ C) :
    let row := earlyExpandedMetricRow height metric expand validate P
    let old := earlyPrefixSeedReadRow G height metric P
    row.bought = old.1.2.1 ∧ row.failed = old.1.2.2.1 ∧ row.searches ≤ old.1.2.2.2 ∧ row.work ≤ B+E+C+8 := by
  subst n
  cases ending : P.getLast? with
  | none =>
    have empty : P = [] := List.getLast?_eq_none_iff.mp ending
    subst P
    exact ⟨rfl,rfl,le_rfl,Nat.le_add_left _ _⟩
  | some d =>
    let next := earlyExpandedMetricRow height metric expand validate P
    let prior := earlyPrefixSeedReadRow G height metric P
    have oldExact : prior.1 = earlyPrefixWorkEntry G height (fun Q => ((metric Q).1,(metric Q).2.1)) P :=
      (earlyPrefixSeedReadRow_spec G height metric B P metricCap).1
    change next.bought = prior.1.2.1 ∧ next.failed = prior.1.2.2.1 ∧
      next.searches ≤ prior.1.2.2.2 ∧ next.work ≤ B+E+C+8
    rw [oldExact]
    obtain ⟨checked,search,work⟩ := validation d
    let priorGraph := (expandLabelledLinksWithSearchWork G heightForestLabel (metric P).1).1
    let priorSearch := reachInWithArcInspections priorGraph d.2 (Fintype.card V)
    have sameMiss : (validate (expand (metric P).1).1 d).1 = decide (d.1 ∉ priorSearch.1) :=
      checked.trans (by dsimp only [priorSearch,priorGraph]; rw [expansion.1])
    have lessSearch : (validate (expand (metric P).1).1 d).2.1 ≤ priorSearch.2 :=
      search.trans (by dsimp only [priorSearch,priorGraph]; rw [expansion.1])
    simp only [next,earlyExpandedMetricRow_apply,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast,ending,earlyPrefixWorkEntry,sameMiss,true_and]
    exact ⟨rfl,Nat.add_le_add (Nat.le_add_right _ _) lessSearch,
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add metricCap expansion.2) work) 8⟩

theorem earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric_compare (G : Arcs V) (n height : ℕ)
    (size : n = Fintype.card V) (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V)
    (support : Arcs (HeightForestVertex V height)) (D : List (V × V)) (B E C : ℕ)
    (expansion : ∀ H ⊆ support, (expand H).1 = (expandLabelledLinksWithSearchWork G heightForestLabel H).1 ∧
      (expand H).2 ≤ E)
    (supported : ∀ P ∈ D.inits, (metric P).1 ⊆ support)
    (metricCap : ∀ P ∈ D.inits, (metric P).2.2 ≤ B)
    (validation : ∀ H ⊆ support, ∀ d,
      let out := validate (expand H).1 d
      let old := reachInWithArcInspections (expand H).1 d.2 n
      out.1 = decide (d.1 ∉ old.1) ∧ out.2.1 ≤ old.2 ∧ out.2.2 ≤ C) :
    let out := earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric G height metric expand validate D
    let old := earlyRoundedGraphWithSeedReadsFromMetric G height metric D
    out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧ out.2.2 ≤ (D.length+1)*(B+E+C+8)+E+6 := by
  let source := D.inits.toFinset
  let read := earlyExpandedMetricRow height metric expand validate
  let prior := earlyPrefixSeedReadRow G height metric
  let rows := source.map read
  let old := source.map prior
  have each (P : List (V × V)) (on : P ∈ source) :=
    earlyExpandedMetricRow_compare G n height size metric expand validate P B E C
      (metricCap P (List.mem_toFinset.mp on)) (expansion _ (supported P (List.mem_toFinset.mp on)))
      (validation _ (supported P (List.mem_toFinset.mp on)))
  have failure : (rows.filter fun r => r.failed = true).Nonempty ↔
      (old.filter fun r => r.1.2.2.1 = true).Nonempty := by
    constructor
    · rintro ⟨r,present⟩
      obtain ⟨mem,miss⟩ := mem_filter.mp present
      obtain ⟨P,on,rfl⟩ := mem_map.mp mem
      exact ⟨prior P,mem_filter.mpr ⟨mem_map_of_mem _ on,(each P on).2.1 ▸ miss⟩⟩
    · rintro ⟨r,present⟩
      obtain ⟨mem,miss⟩ := mem_filter.mp present
      obtain ⟨P,on,rfl⟩ := mem_map.mp mem
      exact ⟨read P,mem_filter.mpr ⟨mem_map_of_mem _ on,(each P on).2.1.symm ▸ miss⟩⟩
  have bought : rows.biUnion ExpandedMetricRow.bought = old.biUnion (fun r => r.1.2.1) := by
    ext e
    constructor
    · intro member
      obtain ⟨r,mem,used⟩ := mem_biUnion.mp member
      obtain ⟨P,on,rfl⟩ := mem_map.mp mem
      exact mem_biUnion.mpr ⟨prior P,mem_map_of_mem _ on,(each P on).1 ▸ used⟩
    · intro member
      obtain ⟨r,mem,used⟩ := mem_biUnion.mp member
      obtain ⟨P,on,rfl⟩ := mem_map.mp mem
      exact mem_biUnion.mpr ⟨read P,mem_map_of_mem _ on,(each P on).1.symm ▸ used⟩
  have holds : rows.biUnion ExpandedMetricRow.bought ⊆ support := by
    intro edge member
    obtain ⟨r,mem,used⟩ := mem_biUnion.mp member
    obtain ⟨P,on,rfl⟩ := mem_map.mp mem
    cases ending : P.getLast? with
    | none =>
      simp only [read,earlyExpandedMetricRow_apply,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast,ending,Finset.notMem_empty] at used
    | some d =>
      exact supported P (List.mem_toFinset.mp on) (by
        simpa only [read,earlyExpandedMetricRow_apply,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast,ending] using used)
  have searchCount : (∑ r ∈ rows,r.searches) ≤ ∑ r ∈ old,r.1.2.2.2 := by
    dsimp only [rows,old]
    rw [sum_map,sum_map]
    exact sum_le_sum (fun P on => (each P on).2.2.1)
  have wordCount : (∑ r ∈ rows,r.work) ≤ (D.length+1)*(B+E+C+8) := by
    dsimp only [rows]
    rw [sum_map]
    calc
      _ ≤ ∑ _P ∈ source,(B+E+C+8) := sum_le_sum fun P on => (each P on).2.2.2
      _ = source.card*(B+E+C+8) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (D.inits.toFinset_card_le.trans_eq (List.length_inits D))
  have final := expansion _ holds
  have finalCost := final.2
  let oldSearch := ∑ r ∈ old,r.1.2.2.2
  let oldWork := ∑ r ∈ old,r.2
  let finalOld := expandLabelledLinksWithSearchWork G heightForestLabel (old.biUnion fun r => r.1.2.1)
  let before : Arcs V × ℕ × ℕ := if (old.filter fun r => r.1.2.2.1 = true).Nonempty then (G,oldSearch,oldWork)
    else (finalOld.1,oldSearch+finalOld.2,oldWork)
  let newSearch := ∑ r ∈ rows,r.searches
  let newWork := ∑ r ∈ rows,r.work
  let finalNew := expand (rows.biUnion ExpandedMetricRow.bought)
  change finalNew.2 ≤ E at finalCost
  let fresh : Arcs V × ℕ × ℕ := if (rows.filter fun r => r.failed = true).Nonempty then (G,newSearch,newWork+6)
    else (finalNew.1,newSearch,newWork+finalNew.2+6)
  change fresh.1 = before.1 ∧ fresh.2.1 ≤ before.2.1 ∧ fresh.2.2 ≤ _
  by_cases fallback : (old.filter fun r => r.1.2.2.1 = true).Nonempty
  · have failed := failure.mpr fallback
    simp only [fresh,before,ite_eq_left failed,ite_eq_left fallback,true_and]
    exact ⟨searchCount,by omega⟩
  · have success := mt failure.mp fallback
    simp only [fresh,before,ite_eq_right success,ite_eq_right fallback]
    exact ⟨final.1.trans (by dsimp only [finalOld]; rw [bought]),searchCount.trans (Nat.le_add_right _ _),
      Nat.add_le_add_right (Nat.add_le_add wordCount finalCost) 6⟩

theorem earlyRoundedGraphWithSeedReadsAndExpansionFromMetric_compare (G : Arcs V) (n height : ℕ)
    (size : n = Fintype.card V) (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (support : Arcs (HeightForestVertex V height)) (D : List (V × V)) (B E : ℕ)
    (expansion : ∀ H ⊆ support, (expand H).1 = (expandLabelledLinksWithSearchWork G heightForestLabel H).1 ∧
      (expand H).2 ≤ E)
    (supported : ∀ P ∈ D.inits, (metric P).1 ⊆ support)
    (metricCap : ∀ P ∈ D.inits, (metric P).2.2 ≤ B) :
    let out := earlyRoundedGraphWithSeedReadsAndExpansionFromMetric G n height metric expand D
    let old := earlyRoundedGraphWithSeedReadsFromMetric G height metric D
    out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧ out.2.2 ≤ (D.length+1)*(B+E+8)+E+6 := by
  simpa only [earlyRoundedGraphWithSeedReadsAndExpansionFromMetric,Nat.add_zero] using
    earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric_compare G n height size metric expand (earlyExpansionArcInspections n)
      support D B E 0 expansion supported metricCap (fun _ _ _ => ⟨rfl,le_rfl,le_rfl⟩)

private def reverseEarlyPrefixWithWordWork {A : Type*} : List A → List A → List A × ℕ
  | [], output => (output,1)
  | a::rest, output =>
    let reversed := reverseEarlyPrefixWithWordWork rest (a::output)
    (reversed.1,reversed.2+3)

private theorem reverseEarlyPrefixWithWordWork_spec {A : Type*} (xs acc : List A) :
    reverseEarlyPrefixWithWordWork xs acc = (xs.reverse ++ acc,3*xs.length+1) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a rest ih =>
    simp only [reverseEarlyPrefixWithWordWork,ih,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons]
    congr 1

private structure CollectedEarlyMetrics (V : Type*) [DecidableEq V] (height : ℕ) where
  links : List (Arcs (HeightForestVertex V height))
  failed : Bool
  searches : ℕ
  work : ℕ

private def collectEarlyMetricsWithWordWork (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) : List (V × V) → List (V × V) → CollectedEarlyMetrics V height
  | _, [] => ⟨[],false,0,2⟩
  | reversed, d :: todo =>
    let extended := d::reversed
    let ordered := reverseEarlyPrefixWithWordWork extended []
    let row := earlyExpandedMetricValueWithLast height metric expand validate ordered.1 (some d)
    let rest := collectEarlyMetricsWithWordWork height metric expand validate extended todo
    ⟨row.bought::rest.links,row.failed || rest.failed,row.searches+rest.searches,
      row.work+rest.work+ordered.2+28⟩

private theorem nonemptyEarlyPrefixes_cons {A : Type*} (previous todo : List A) (d : A) :
    (List.inits (d::todo)).tail.map (fun P => previous++P) =
      (previous++[d]) :: (todo.inits.tail.map (fun P => (previous++[d])++P)) := by
  rw [List.inits_cons,List.tail_cons,List.map_map]
  cases todo with
  | nil => simp
  | cons e more => simp [List.map_map, Function.comp_def,List.append_assoc]

omit [Fintype V] in
private theorem collectEarlyMetricsWithWordWork_spec (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) (reversed D : List (V × V)) :
    let out := collectEarlyMetricsWithWordWork height metric expand validate reversed D
    let rows := (D.inits.tail.map (fun P => reversed.reverse++P)).map (earlyExpandedMetricValue height metric expand validate)
    out.links = rows.map ExpandedMetricRow.bought ∧ out.failed = rows.any ExpandedMetricRow.failed ∧
      out.searches = (rows.map ExpandedMetricRow.searches).sum ∧
      out.work ≤ (rows.map ExpandedMetricRow.work).sum + D.length*(3*(reversed.length+D.length)+29)+2 := by
  induction D generalizing reversed with
  | nil => simp [collectEarlyMetricsWithWordWork]
  | cons d todo ih =>
    let read := earlyExpandedMetricValue height metric expand validate
    let P := reversed.reverse++[d]
    let rows := (todo.inits.tail.map (fun Q => (d::reversed).reverse++Q)).map read
    let rest := collectEarlyMetricsWithWordWork height metric expand validate (d::reversed) todo
    have root : P.getLast? = some d := by simp [P]
    have same : earlyExpandedMetricValueWithLast height metric expand validate P (some d) = read P := by
      dsimp only [read,earlyExpandedMetricValue]
      rw [root]
    have shape : ((d::todo).inits.tail.map (fun Q => reversed.reverse++Q)).map read = read P :: rows := by
      rw [nonemptyEarlyPrefixes_cons,List.map_cons]
      simp only [P,rows,List.reverse_cons]
    obtain ⟨links,failed,searches,work⟩ := ih (d::reversed)
    dsimp only
    change (collectEarlyMetricsWithWordWork height metric expand validate reversed (d::todo)).links =
      (((d::todo).inits.tail.map (fun Q => reversed.reverse++Q)).map read).map ExpandedMetricRow.bought ∧
      _
    rw [shape]
    simp only [collectEarlyMetricsWithWordWork,reverseEarlyPrefixWithWordWork_spec,List.reverse_cons,List.append_nil]
    change (earlyExpandedMetricValueWithLast height metric expand validate P (some d)).bought::rest.links =
        (read P :: rows).map ExpandedMetricRow.bought ∧
      ((earlyExpandedMetricValueWithLast height metric expand validate P (some d)).failed || rest.failed) =
        (read P :: rows).any ExpandedMetricRow.failed ∧
      (earlyExpandedMetricValueWithLast height metric expand validate P (some d)).searches+rest.searches =
        ((read P :: rows).map ExpandedMetricRow.searches).sum ∧
      (earlyExpandedMetricValueWithLast height metric expand validate P (some d)).work+rest.work+
          (3*(reversed.length+1)+1)+28 ≤
        ((read P :: rows).map ExpandedMetricRow.work).sum + (todo.length+1)*(3*(reversed.length+(todo.length+1))+29)+2
    rw [same]
    change rest.links = rows.map ExpandedMetricRow.bought at links
    change rest.failed = rows.any ExpandedMetricRow.failed at failed
    change rest.searches = (rows.map ExpandedMetricRow.searches).sum at searches
    change rest.work ≤ _ at work
    simp only [List.map_cons,List.any_cons,List.sum_cons,links,failed,searches,true_and]
    change rest.work ≤ (rows.map ExpandedMetricRow.work).sum + todo.length*(3*(reversed.length+1+todo.length)+29)+2 at work
    have room : reversed.length+1+todo.length = reversed.length+(todo.length+1) := by omega
    rw [room] at work
    rw [Nat.succ_mul todo.length (3*(reversed.length+(todo.length+1))+29)]
    omega

private def unionEarlyMetricLinksWithWordWork {A : Type*} [DecidableEq A] : List (Finset A) → Finset A × ℕ
  | [] => (∅,2)
  | H::others =>
    let rest := unionEarlyMetricLinksWithWordWork others
    let combined := unionFinsetWithWordWork H rest.1
    (combined.1,rest.2+combined.2+5)

private theorem unionEarlyMetricLinksWithWordWork_spec {A : Type*} [DecidableEq A] (support : Finset A)
    (links : List (Finset A)) (supported : ∀ H ∈ links, H ⊆ support) :
    let union := unionEarlyMetricLinksWithWordWork links
    (∀ e, e ∈ union.1 ↔ ∃ H ∈ links, e ∈ H) ∧ union.1 ⊆ support ∧
      union.2 ≤ links.length*(support.card*(12*support.card+19)+5*support.card+15)+2 := by
  induction links with
  | nil => simp [unionEarlyMetricLinksWithWordWork]
  | cons H links ih =>
    let prior := unionEarlyMetricLinksWithWordWork links
    have this : H ⊆ support := supported H List.mem_cons_self
    obtain ⟨members,contained,work⟩ := ih (fun K on => supported K (List.mem_cons_of_mem _ on))
    obtain ⟨exact,cost⟩ := unionFinsetWithWordWork_spec H prior.1
    have cap : (unionFinsetWithWordWork H prior.1).2 ≤ support.card*(12*support.card+19)+5*support.card+10 :=
      cost.trans (by gcongr)
    change (∀ e, e ∈ (unionFinsetWithWordWork H prior.1).1 ↔ _) ∧
      (unionFinsetWithWordWork H prior.1).1 ⊆ support ∧ prior.2+(unionFinsetWithWordWork H prior.1).2+5 ≤ _
    rw [exact]
    refine ⟨?_,union_subset this contained,?_⟩
    · intro e
      rw [mem_union,members e]
      simp only [List.mem_cons,exists_eq_or_imp]
    · rw [List.length_cons,Nat.succ_mul links.length (support.card*(12*support.card+19)+5*support.card+15)]
      change prior.2 ≤ links.length*(support.card*(12*support.card+19)+5*support.card+15)+2 at work
      omega

/-- Starting with the empty prefix, extend the reversed history one request
at a time. Each nonempty prefix is read once using its known final request.
Merge the bought graphs only when the checks all succeed. -/
def earlyRoundedGraphWithMeasuredPrefixAssembly (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) (D : List (V × V)) : Arcs V × ℕ × ℕ :=
  let collected := collectEarlyMetricsWithWordWork height metric expand validate [] D
  if collected.failed then (G,collected.searches,collected.work+14) else
    let combined := unionEarlyMetricLinksWithWordWork collected.links
    let expanded := expand combined.1
    (expanded.1,collected.searches,collected.work+combined.2+expanded.2+14)

def earlyPrefixAssemblyWordBudget (p links : ℕ) : ℕ :=
  p*(3*p+29) + p*(links*(12*links+19)+5*links+15) + 4

theorem earlyPrefixAssemblyWordBudget_le {p p' b b' : ℕ} (prefixes : p ≤ p') (links : b ≤ b') :
    earlyPrefixAssemblyWordBudget p b ≤ earlyPrefixAssemblyWordBudget p' b' := by
  unfold earlyPrefixAssemblyWordBudget
  gcongr

private theorem early_inits_nodup {A : Type*} (D : List A) : D.inits.Nodup := by
  induction D with
  | nil => simp
  | cons a D ih =>
    rw [List.inits_cons]
    refine List.nodup_cons.mpr ⟨?_,ih.map (fun _ _ eq => (List.cons.inj eq).2)⟩
    simp

omit [Fintype V] in
/-- Measured assembly has the same graph and ordinary search tally as the
prefix-table implementation. The additional bound covers building prefix
lists, collecting the failure flags and work, and merging bought links. -/
theorem earlyRoundedGraphWithMeasuredPrefixAssembly_compare (G : Arcs V) (height : ℕ)
    (metric : List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (expand : Arcs (HeightForestVertex V height) → Arcs V × ℕ)
    (validate : EarlyExpansionValidation V) (D : List (V × V))
    (support : Arcs (HeightForestVertex V height)) (supported : ∀ P ∈ D.inits, (metric P).1 ⊆ support) :
    let out := earlyRoundedGraphWithMeasuredPrefixAssembly G height metric expand validate D
    let old := earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric G height metric expand validate D
    out.1 = old.1 ∧ out.2.1 = old.2.1 ∧
      out.2.2 ≤ old.2.2 + earlyPrefixAssemblyWordBudget D.length support.card := by
  let read := earlyExpandedMetricValue height metric expand validate
  let rows := D.inits.tail.map read
  let collected := collectEarlyMetricsWithWordWork height metric expand validate [] D
  let old := D.inits.toFinset.map (earlyExpandedMetricRow height metric expand validate)
  have fullRows : D.inits.map read = read [] :: rows := by
    cases D <;> simp [rows]
  have member (r) : r ∈ old ↔ r ∈ D.inits.map read := by
    simp only [old,mem_map,List.mem_toFinset,List.mem_map,earlyExpandedMetricRow_apply,read]
  have rowSum (f : ExpandedMetricRow V height → ℕ) :
      ∑ r ∈ old, f r = ((D.inits.map read).map f).sum := by
    simp only [old,sum_map,List.sum_toFinset _ (early_inits_nodup D),List.map_map]
    rfl
  obtain ⟨links,failed,searches,work⟩ := collectEarlyMetricsWithWordWork_spec height metric expand validate [] D
  have chosen : collected.links = rows.map ExpandedMetricRow.bought := by simpa [collected,rows,read] using links
  have missed : collected.failed = rows.any ExpandedMetricRow.failed := by simpa [collected,rows,read] using failed
  have searched : collected.searches = ∑ r ∈ old, r.searches := by
    rw [rowSum _,fullRows,List.map_cons,List.sum_cons]
    change collected.searches = 0+(rows.map ExpandedMetricRow.searches).sum
    simpa [collected,rows,read] using searches
  have charged : collected.work ≤ (∑ r ∈ old,r.work) + D.length*(3*D.length+29)+2-8 := by
    have tally : collected.work ≤ (rows.map ExpandedMetricRow.work).sum + D.length*(3*D.length+29)+2 := by
      simpa [collected,rows,read] using work
    rw [rowSum _,fullRows,List.map_cons,List.sum_cons]
    change collected.work ≤ 8+(rows.map ExpandedMetricRow.work).sum+D.length*(3*D.length+29)+2-8
    omega
  have failure : (old.filter fun r => r.failed = true).Nonempty ↔ collected.failed = true := by
    rw [filter_nonempty_iff,missed,List.any_eq_true]
    constructor
    · rintro ⟨r,on,miss⟩
      have seen := (member r).mp on
      rw [fullRows] at seen
      rcases List.mem_cons.mp seen with rfl | after
      · simp [read,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast] at miss
      · exact ⟨r,after,miss⟩
    · rintro ⟨r,on,miss⟩
      exact ⟨r,(member r).mpr (fullRows.symm ▸ List.mem_cons_of_mem _ on),miss⟩
  have contained (H) (on : H ∈ collected.links) : H ⊆ support := by
    rw [chosen] at on
    obtain ⟨r,rowOn,rowEquals⟩ := List.mem_map.mp on
    subst H
    obtain ⟨P,prefixOn,prefixEquals⟩ := List.mem_map.mp (show r ∈ D.inits.tail.map read from rowOn)
    subst r
    have cap := supported P (List.mem_of_mem_tail prefixOn)
    cases endOf : P.getLast? with
    | none => simp [read,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast,endOf]
    | some d => simpa only [read,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast,endOf] using cap
  let combined := unionEarlyMetricLinksWithWordWork collected.links
  obtain ⟨edgeIn,_,fee⟩ := unionEarlyMetricLinksWithWordWork_spec support collected.links contained
  have exactUnion : combined.1 = old.biUnion ExpandedMetricRow.bought := by
    ext e
    change e ∈ (unionEarlyMetricLinksWithWordWork collected.links).1 ↔ _
    rw [edgeIn e]
    constructor
    · rintro ⟨H,on,used⟩
      rw [chosen] at on
      obtain ⟨r,rowOn,rowEquals⟩ := List.mem_map.mp on
      exact mem_biUnion.mpr ⟨r,(member r).mpr (fullRows.symm ▸ List.mem_cons_of_mem _ rowOn),rowEquals.symm ▸ used⟩
    · intro used
      obtain ⟨r,on,edge⟩ := mem_biUnion.mp used
      have seen := (member r).mp on
      rw [fullRows] at seen
      rcases List.mem_cons.mp seen with rfl | after
      · simp [read,earlyExpandedMetricValue,earlyExpandedMetricValueWithLast] at edge
      · exact ⟨r.bought,chosen.symm ▸ List.mem_map_of_mem after,edge⟩
  have feeCap : combined.2 ≤ D.length*(support.card*(12*support.card+19)+5*support.card+15)+2 := by
    have length : collected.links.length = D.length := by
      rw [chosen,List.length_map]
      simp only [rows,List.length_map,List.length_tail,List.length_inits,Nat.add_sub_cancel]
    simpa only [combined,length] using fee
  have enough : 8 ≤ ∑ r ∈ old,r.work := by
    rw [rowSum _,fullRows,List.map_cons,List.sum_cons]
    exact Nat.le_add_right _ _
  have charges : collected.work + 8 ≤ (∑ r ∈ old,r.work) + D.length*(3*D.length+29)+2 := by omega
  let fresh : Arcs V × ℕ × ℕ := if collected.failed = true then (G,collected.searches,collected.work+14) else
    ((expand combined.1).1,collected.searches,collected.work+combined.2+(expand combined.1).2+14)
  let prior : Arcs V × ℕ × ℕ := if (old.filter fun r => r.failed = true).Nonempty then
    (G,(∑ r ∈ old,r.searches),(∑ r ∈ old,r.work)+6) else
    let expanded := expand (old.biUnion ExpandedMetricRow.bought)
    (expanded.1,(∑ r ∈ old,r.searches),(∑ r ∈ old,r.work)+expanded.2+6)
  change fresh.1 = prior.1 ∧ fresh.2.1 = prior.2.1 ∧ fresh.2.2 ≤ prior.2.2 + _
  by_cases misses : collected.failed = true
  · have miss := failure.mpr misses
    dsimp only [fresh,prior]
    rw [ite_eq_left misses,ite_eq_left miss]
    refine ⟨rfl,searched,?_⟩
    change collected.work+14 ≤ (∑ r ∈ old,r.work)+6 + earlyPrefixAssemblyWordBudget D.length support.card
    unfold earlyPrefixAssemblyWordBudget
    omega
  · have pass := mt failure.mp misses
    dsimp only [fresh,prior]
    rw [ite_eq_right misses,ite_eq_right pass]
    refine ⟨congrArg (fun H => (expand H).1) exactUnion,searched,?_⟩
    change collected.work+combined.2+(expand combined.1).2+14 ≤
      (∑ r ∈ old,r.work)+(expand (old.biUnion ExpandedMetricRow.bought)).2+6 + earlyPrefixAssemblyWordBudget D.length support.card
    rw [exactUnion]
    unfold earlyPrefixAssemblyWordBudget
    omega

end OnlineReachabilityPreservers
