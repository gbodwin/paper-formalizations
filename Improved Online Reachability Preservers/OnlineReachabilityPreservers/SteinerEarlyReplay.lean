import OnlineReachabilityPreservers.AlgorithmSearchWork
import OnlineReachabilityPreservers.SeparatorWork
import OnlineReachabilityPreservers.SteinerEarlyRound

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

end OnlineReachabilityPreservers
