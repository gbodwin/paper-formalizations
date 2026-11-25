import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.Growth

/-! Algorithm 3 and Theorem 15. The path rule is a parameter of the reduction. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V]

abbrev PathRule (V : Type*) := Arcs V → V × V → Option (List (V × V))

def pathArcs (path : Option (List (V × V))) : Arcs V := (path.getD []).toFinset

def runRule (choose : PathRule V) (H : Arcs V) (D : List (V × V)) : Arcs V :=
  D.foldl (fun A d => A ∪ pathArcs (choose A d)) H

/-- Select the lexicographically first candidate whose new edges exceed the budget. -/
def expensive (choose : PathRule V) (p F : ℕ) (H : Arcs V) (Q : Finset (V × V)) :
    Option (V × V) :=
  (least? ((Q.filter (fun d => F < p * (pathArcs (choose H d) \ H).card)).image toLex)).map ofLex

private theorem expensive_some {choose : PathRule V} {p F : ℕ} {H Q : Arcs V} {d : V × V}
    (h : expensive choose p F H Q = some d) :
    d ∈ Q ∧ F < p * (pathArcs (choose H d) \ H).card := by
  unfold expensive at h
  cases ho : least? ((Q.filter (fun d => F < p * (pathArcs (choose H d) \ H).card)).image toLex) with
  | none => simp [ho] at h
  | some a =>
    have he : ofLex a = d := by simpa [ho] using h
    obtain ⟨q, hq, rfl⟩ := mem_image.mp (least?_mem ho)
    exact he ▸ mem_filter.mp hq

private theorem expensive_none {choose : PathRule V} {p F : ℕ} {H Q : Arcs V}
    (h : expensive choose p F H Q = none) {d : V × V} (hd : d ∈ Q) :
    p * (pathArcs (choose H d) \ H).card ≤ F := by
  by_contra! hlt
  have hm : toLex d ∈ (Q.filter (fun x => F < p * (pathArcs (choose H x) \ H).card)).image toLex :=
    mem_image.mpr ⟨d, mem_filter.mpr ⟨hd, hlt⟩, rfl⟩
  obtain ⟨e, he⟩ := least?_some ⟨_, hm⟩
  simp [expensive, he] at h

/-- Simulate purchases whose new edges would exceed the per-request budget.
The first phase ignores already assigned pairs. -/
def expensiveTrace (choose : PathRule V) (p F : ℕ) :
    ℕ → Arcs V → Finset (V × V) → List (V × V)
  | 0, _, _ => []
  | k + 1, H, Q =>
    match expensive choose p F H Q with
    | none => []
    | some d => d :: expensiveTrace choose p F k (H ∪ pathArcs (choose H d)) (Q.erase d)

private theorem expensiveTrace_spec (choose : PathRule V) (p F k : ℕ) (H Q : Arcs V) :
    let T := expensiveTrace choose p F k H Q
    let A := runRule choose H T
    T.length ≤ k ∧ T.Nodup ∧
      (∀ d ∈ T, d ∈ Q) ∧
      p * H.card + F * T.length ≤ p * A.card ∧
      (T ≠ [] → p * H.card + F * T.length < p * A.card) ∧
      (T.length < k → ∀ d ∈ Q, d ∉ T → p * (pathArcs (choose A d) \ A).card ≤ F) := by
  induction k generalizing H Q with
  | zero => simp [expensiveTrace, runRule]
  | succ k ih =>
    cases hs : expensive choose p F H Q with
    | none =>
      simp [expensiveTrace, hs, runRule]
      exact fun _ _ hd => expensive_none hs hd
    | some b =>
      let J := H ∪ pathArcs (choose H b)
      let U := expensiveTrace choose p F k J (Q.erase b)
      have hb := expensive_some hs
      obtain ⟨hU, hn, hQ, hcost, _, hfreeze⟩ := ih J (Q.erase b)
      change U.length ≤ k at hU
      change p * J.card + F * U.length ≤ p * (runRule choose J U).card at hcost
      change U.length < k → ∀ d ∈ Q.erase b, d ∉ U →
        p * (pathArcs (choose (runRule choose J U) d) \ runRule choose J U).card ≤ F at hfreeze
      have hcard : J.card = (pathArcs (choose H b) \ H).card + H.card := by
        rw [card_sdiff_add_card, union_comm]
      have hc : p * H.card + F < p * J.card := by
        rw [hcard, Nat.mul_add]
        omega
      simp only [expensiveTrace, hs, List.length_cons, List.nodup_cons, List.mem_cons]
      change U.length + 1 ≤ k + 1 ∧ (b ∉ U ∧ U.Nodup) ∧
        (∀ d, d = b ∨ d ∈ U → d ∈ Q) ∧
        p * H.card + F * (U.length + 1) ≤ p * (runRule choose J U).card ∧
        ((b :: U) ≠ [] → p * H.card + F * (U.length + 1) < p * (runRule choose J U).card) ∧
        (U.length + 1 < k + 1 →
          ∀ d ∈ Q, ¬(d = b ∨ d ∈ U) →
            p * (pathArcs (choose (runRule choose J U) d) \ runRule choose J U).card ≤ F)
      have hlt : p * H.card + F * (U.length + 1) < p * (runRule choose J U).card := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      refine ⟨by omega, ⟨fun h => (mem_erase.mp (hQ b h)).1 rfl, hn⟩, ?_, hlt.le, fun _ => hlt, ?_⟩
      · intro d hd
        rcases hd with rfl | hm
        · exact hb.1
        · exact (mem_erase.mp (hQ d hm)).2
      · intro hk d hd hnD
        exact hfreeze (by omega) d (mem_erase.mpr ⟨fun h => hnD (Or.inl h), hd⟩)
          (fun h => hnD (Or.inr h))

private theorem runRule_extends (choose : PathRule V) (H : Arcs V) (D : List (V × V)) :
    H ⊆ runRule choose H D := by
  induction D generalizing H with
  | nil => exact Subset.rfl
  | cons d ds ih => exact subset_union_left.trans (ih (H ∪ pathArcs (choose H d)))

/-- Reconstruct the path at the moment the pair was finalized, or use the frozen state. -/
def assignedPath (choose : PathRule V) (H : Arcs V) :
    List (V × V) → V × V → Option (List (V × V))
  | [], d => choose H d
  | a :: as, d => if a = d then choose H a else assignedPath choose (H ∪ pathArcs (choose H a)) as d

private theorem assignedPath_paid (choose : PathRule V) (H : Arcs V) (T : List (V × V))
    (d : V × V) (hd : d ∈ T) : pathArcs (assignedPath choose H T d) ⊆ runRule choose H T := by
  induction T generalizing H with
  | nil => simp at hd
  | cons a as ih =>
    by_cases eq : a = d
    · subst a
      simp only [assignedPath]
      exact subset_union_right.trans (runRule_extends choose _ as)
    · simp only [assignedPath, ite_eq_right eq]
      exact ih (H ∪ pathArcs (choose H a)) ((List.mem_cons.mp hd).resolve_left (Ne.symm eq))

private theorem assignedPath_frozen (choose : PathRule V) (H : Arcs V) (T : List (V × V))
    (d : V × V) (hd : d ∉ T) : assignedPath choose H T d = choose (runRule choose H T) d := by
  induction T generalizing H with
  | nil => rfl
  | cons a as ih =>
    have ne : a ≠ d := fun h => hd (List.mem_cons.mpr (Or.inl h.symm))
    simp only [assignedPath, ite_eq_right ne]
    exact ih (H ∪ pathArcs (choose H a)) (fun h => hd (List.mem_cons.mpr (Or.inr h)))

/-- The reconstructed path comes from a state contained in the final replay state. -/
theorem assignedPath_uses_state (choose : PathRule V) (H : Arcs V) (T : List (V × V))
    (d : V × V) :
    ∃ A ⊆ runRule choose H T, assignedPath choose H T d = choose A d := by
  induction T generalizing H with
  | nil => exact ⟨H, Subset.rfl, rfl⟩
  | cons q qs ih =>
    by_cases h : q = d
    · subst q
      exact ⟨H, runRule_extends choose H _, by simp [assignedPath]⟩
    · obtain ⟨A, hs, he⟩ := ih (H ∪ pathArcs (choose H q))
      exact ⟨A, hs, by simpa [assignedPath, h] using he⟩

def knownBudgetPath (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ) (d : V × V) :
    Option (List (V × V)) :=
  assignedPath choose ∅ (expensiveTrace choose p F p ∅ Q) d

private def expensiveTraceWithChoiceCalls (choose : PathRule V) (p F : ℕ) :
    ℕ → Arcs V → Finset (V × V) → List (V × V) × ℕ
  | 0, _, _ => ([], 0)
  | k + 1, H, Q =>
    match expensive choose p F H Q with
    | none => ([], Q.card)
    | some d =>
      let rest := expensiveTraceWithChoiceCalls choose p F k (H ∪ pathArcs (choose H d)) (Q.erase d)
      (d :: rest.1, Q.card + 1 + rest.2)

private theorem expensiveTraceWithChoiceCalls_spec (choose : PathRule V) (p F k : ℕ) (H Q : Arcs V) :
    let result := expensiveTraceWithChoiceCalls choose p F k H Q
    result.1 = expensiveTrace choose p F k H Q ∧ result.2 ≤ k * (Q.card + 1) := by
  induction k generalizing H Q with
  | zero => simp [expensiveTraceWithChoiceCalls, expensiveTrace]
  | succ k ih =>
    cases h : expensive choose p F H Q with
    | none =>
      simp only [expensiveTraceWithChoiceCalls, expensiveTrace, h, true_and]
      rw [Nat.succ_mul k (Q.card + 1)]
      omega
    | some d =>
      obtain ⟨result, calls⟩ := ih (H ∪ pathArcs (choose H d)) (Q.erase d)
      simp only [expensiveTraceWithChoiceCalls, expensiveTrace, h, result, true_and]
      have cap : (Q.erase d).card ≤ Q.card := card_le_card (erase_subset _ _)
      have tail := calls.trans (Nat.mul_le_mul_left k (Nat.succ_le_succ cap))
      exact (Nat.add_le_add (le_rfl : Q.card + 1 ≤ Q.card + 1) tail).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul k (Q.card + 1)).symm)


private def assignedPathWithChoiceCalls (choose : PathRule V) (H : Arcs V) :
    List (V × V) → V × V → Option (List (V × V)) × ℕ
  | [], d => (choose H d, 1)
  | a :: as, d =>
    if a = d then (choose H a, 1)
    else
      let tail := assignedPathWithChoiceCalls choose (H ∪ pathArcs (choose H a)) as d
      (tail.1, tail.2 + 1)

private theorem assignedPathWithChoiceCalls_spec (choose : PathRule V) (H : Arcs V) (T : List (V × V))
    (d : V × V) :
    let result := assignedPathWithChoiceCalls choose H T d
    result.1 = assignedPath choose H T d ∧ result.2 ≤ T.length + 1 := by
  induction T generalizing H with
  | nil => simp [assignedPathWithChoiceCalls, assignedPath]
  | cons a T ih =>
    by_cases h : a = d
    · simp [assignedPathWithChoiceCalls, assignedPath, h]
    · obtain ⟨result, count⟩ := ih (H ∪ pathArcs (choose H a))
      simp only [assignedPathWithChoiceCalls, assignedPath, h, ↓reduceIte, result, true_and, List.length_cons]
      exact Nat.succ_le_succ count

/-- Compute the usual known-quota path and count requests to its base
path rule. The estimate includes the initial scans and final replay. -/
def knownBudgetPathWithChoiceCalls (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let planned := expensiveTraceWithChoiceCalls choose p F p ∅ Q
  let selected := assignedPathWithChoiceCalls choose ∅ planned.1 d
  (selected.1, planned.2 + selected.2)

theorem knownBudgetPathWithChoiceCalls_spec (choose : PathRule V) (Q : Finset (V × V))
    (p F : ℕ) (d : V × V) :
    let result := knownBudgetPathWithChoiceCalls choose Q p F d
    result.1 = knownBudgetPath choose Q p F d ∧ result.2 ≤ p * (Q.card + 1) + (p + 1) := by
  let planned := expensiveTraceWithChoiceCalls choose p F p ∅ Q
  obtain ⟨trace, tc⟩ := expensiveTraceWithChoiceCalls_spec choose p F p ∅ Q
  obtain ⟨selection, sc⟩ := assignedPathWithChoiceCalls_spec choose ∅ planned.1 d
  have length := (expensiveTrace_spec choose p F p ∅ Q).1
  change planned.1 = _ at trace
  change (assignedPathWithChoiceCalls choose ∅ planned.1 d).1 = _ at selection
  refine ⟨selection.trans ?_, Nat.add_le_add tc ?_⟩
  · rw [knownBudgetPath, trace]
  · exact sc.trans (Nat.succ_le_succ (by simpa only [trace] using length))

/-- A budget is certified by running the expensive-pair phase and checking its
length and edge count. Both checks depend only on the rule, domain, and quota. -/
def KnownBudgetCertified (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ) : Prop :=
  let T := expensiveTrace choose p F p ∅ Q
  T.length < p ∧ (runRule choose ∅ T).card ≤ F

instance (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ) :
    Decidable (KnownBudgetCertified choose Q p F) := by
  unfold KnownBudgetCertified
  infer_instance

theorem knownBudget_certify (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ)
    (hp : 0 < p)
    (budget : ∀ T : List (V × V), T.Nodup → (∀ d ∈ T, d ∈ Q) → T.length ≤ p →
      (runRule choose ∅ T).card ≤ F) : KnownBudgetCertified choose Q p F := by
  let T := expensiveTrace choose p F p ∅ Q
  let A := runRule choose ∅ T
  obtain ⟨hlt, hn, hQ, _, hprice, _⟩ := expensiveTrace_spec choose p F p ∅ Q
  have hA : A.card ≤ F := budget T hn hQ hlt
  have hshort : T.length < p := by
    by_contra! h
    have he : T.length = p := le_antisymm hlt h
    have hne : T ≠ [] := by
      intro hnil
      simp [hnil] at he
      omega
    have hcost := hprice hne
    change p * (∅ : Arcs V).card + F * T.length < p * A.card at hcost
    rw [he, card_empty, Nat.mul_zero, zero_add, mul_comm F p] at hcost
    exact (not_lt_of_ge (Nat.mul_le_mul_left p hA)) hcost
  exact ⟨hshort,hA⟩

/-- The smallest certified budget up to the given edge cap. -/
def certifiedBudget (choose : PathRule V) (Q : Finset (V × V)) (p cap : ℕ) : ℕ :=
  (least? ((range (cap+1)).filter (KnownBudgetCertified choose Q p))).getD cap

private def certifiedBudgetWorkEntry (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ) :
    ℕ × Bool × ℕ :=
  let trace := expensiveTraceWithChoiceCalls choose p F p ∅ Q
  (F, decide (trace.1.length < p ∧ (runRule choose ∅ trace.1).card ≤ F), trace.2 + trace.1.length)

/-- Count the base path evaluations in the finite quota certification.
Store each evaluated candidate before selecting the budget and totaling
the planned path calls. -/
def certifiedBudgetWithChoiceCalls (choose : PathRule V) (Q : Finset (V × V)) (p cap : ℕ) : ℕ × ℕ :=
  let evaluated := (range (cap + 1)).image (certifiedBudgetWorkEntry choose Q p)
  let certified := (evaluated.filter (fun entry => entry.2.1 = true)).image Prod.fst
  ((least? certified).getD cap, ∑ entry ∈ evaluated, entry.2.2)

theorem certifiedBudgetWithChoiceCalls_spec (choose : PathRule V) (Q : Finset (V × V)) (p cap : ℕ) :
    let result := certifiedBudgetWithChoiceCalls choose Q p cap
    result.1 = certifiedBudget choose Q p cap ∧
      result.2 ≤ (cap + 1) * (p * (Q.card + 1) + p) := by
  let attempts := range (cap + 1)
  let entry := certifiedBudgetWorkEntry choose Q p
  have agrees (F : ℕ) : (entry F).2.1 = true ↔ KnownBudgetCertified choose Q p F := by
    change decide _ = true ↔ _
    rw [decide_eq_true_eq, KnownBudgetCertified, (expensiveTraceWithChoiceCalls_spec choose p F p ∅ Q).1]
  refine ⟨?_, ?_⟩
  · have same : ((attempts.image entry).filter (fun x => x.2.1 = true)).image Prod.fst =
        attempts.filter (KnownBudgetCertified choose Q p) := by
      ext F
      constructor
      · rintro h
        obtain ⟨value, valueFound, budget⟩ := mem_image.mp h
        obtain ⟨inImage, passed⟩ := mem_filter.mp valueFound
        obtain ⟨candidate, hc, rfl⟩ := mem_image.mp inImage
        change candidate = F at budget
        subst candidate
        exact mem_filter.mpr ⟨hc, (agrees F).mp passed⟩
      · intro h
        obtain ⟨candidate, good⟩ := mem_filter.mp h
        exact mem_image.mpr ⟨entry F, mem_filter.mpr ⟨mem_image_of_mem _ candidate, (agrees F).mpr good⟩, rfl⟩
    exact congrArg (fun limits => (least? limits).getD cap) same
  · change (∑ x ∈ attempts.image entry, x.2.2) ≤ _
    rw [sum_image (fun a _ b _ eq => congrArg Prod.fst eq)]
    calc
      _ ≤ ∑ _ ∈ attempts, (p * (Q.card + 1) + p) := by
        apply sum_le_sum
        intro F _
        obtain ⟨trace, calls⟩ := expensiveTraceWithChoiceCalls_spec choose p F p ∅ Q
        change (expensiveTraceWithChoiceCalls choose p F p ∅ Q).2 +
          (expensiveTraceWithChoiceCalls choose p F p ∅ Q).1.length ≤ _
        rw [trace]
        exact Nat.add_le_add calls (expensiveTrace_spec choose p F p ∅ Q).1
      _ = _ := by simp [attempts]

theorem certifiedBudget_spec {choose : PathRule V} {Q : Finset (V × V)} {p cap : ℕ}
    (hcap : KnownBudgetCertified choose Q p cap) :
    KnownBudgetCertified choose Q p (certifiedBudget choose Q p cap) ∧
      ∀ F, KnownBudgetCertified choose Q p F → certifiedBudget choose Q p cap ≤ F := by
  let options := (range (cap+1)).filter (KnownBudgetCertified choose Q p)
  have hc : cap ∈ options := mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self _), hcap⟩
  obtain ⟨b,hb⟩ := least?_some ⟨cap,hc⟩
  have eq : certifiedBudget choose Q p cap = b := by
    change (least? options).getD cap = b
    simp [hb]
  rw [eq]
  refine ⟨(mem_filter.mp (least?_mem hb)).2, fun F hF => ?_⟩
  by_cases h : F ≤ cap
  · exact least?_le hb (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le h), hF⟩)
  · exact (least?_le hb hc).trans (le_of_not_ge h)

theorem theorem15_certified_budget (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ)
    (hp : 0 < p) (certificate : KnownBudgetCertified choose Q p F)
    (P : Finset (V × V)) (sub : P ⊆ Q) (hP : P.card ≤ p) :
    (P.biUnion (fun d => pathArcs (knownBudgetPath choose Q p F d))).card ≤ 2 * F := by
  let T := expensiveTrace choose p F p ∅ Q
  let A := runRule choose ∅ T
  obtain ⟨hshort,hA⟩ := certificate
  change T.length < p at hshort
  change A.card ≤ F at hA
  obtain ⟨_, _, _, _, _, hfreeze⟩ := expensiveTrace_spec choose p F p ∅ Q
  let R d := pathArcs (knownBudgetPath choose Q p F d)
  have hmissing (d : V × V) (hd : d ∈ P) : p * (R d \ A).card ≤ F := by
    by_cases h : d ∈ T
    · have hs : R d ⊆ A := assignedPath_paid choose ∅ T d h
      have he : R d \ A = ∅ := sdiff_eq_empty_iff_subset.mpr hs
      simp [he]
    · change p * (pathArcs (assignedPath choose ∅ T d) \ A).card ≤ F
      rw [assignedPath_frozen choose ∅ T d h]
      exact hfreeze hshort d (sub hd) h
  have hsum : p * (∑ d ∈ P, (R d \ A).card) ≤ p * F := by
    rw [mul_sum]
    calc
      _ ≤ ∑ _d ∈ P, F := sum_le_sum hmissing
      _ = P.card * F := by simp
      _ ≤ p * F := Nat.mul_le_mul_right F hP
  have hsum' : (∑ d ∈ P, (R d \ A).card) ≤ F := Nat.le_of_mul_le_mul_left hsum hp
  have hsub : P.biUnion R ⊆ A ∪ P.biUnion (fun d => R d \ A) := by
    intro e he
    by_cases hh : e ∈ A
    · exact mem_union_left _ hh
    · obtain ⟨d, hd, hr⟩ := mem_biUnion.mp he
      exact mem_union_right _ (mem_biUnion.mpr ⟨d, hd, mem_sdiff.mpr ⟨hr, hh⟩⟩)
  calc
    _ ≤ (A ∪ P.biUnion (fun d => R d \ A)).card := card_le_card hsub
    _ ≤ A.card + (P.biUnion (fun d => R d \ A)).card := card_union_le _ _
    _ ≤ A.card + (∑ d ∈ P, (R d \ A).card) := Nat.add_le_add_left card_biUnion_le _
    _ ≤ 2 * F := by omega

/-- Theorem 15. For any p-bounded set of requests, the preassigned paths have at most
twice the prefix budget of the online path rule. -/
theorem theorem15_known_budget (choose : PathRule V) (Q : Finset (V × V)) (p F : ℕ)
    (hp : 0 < p)
    (budget : ∀ T : List (V × V), T.Nodup → (∀ d ∈ T, d ∈ Q) → T.length ≤ p →
      (runRule choose ∅ T).card ≤ F)
    (P : Finset (V × V)) (sub : P ⊆ Q) (hP : P.card ≤ p) :
    (P.biUnion (fun d => pathArcs (knownBudgetPath choose Q p F d))).card ≤ 2 * F :=
  theorem15_certified_budget choose Q p F hp (knownBudget_certify choose Q p F hp budget) P sub hP

/-- A fixed path is produced by the original rule on one of the simulated substates. -/
theorem knownBudgetPath_valid (choose : PathRule V) (G : Arcs V) (Q : Finset (V × V))
    (p F : ℕ) (d : V × V) (hd : d ∈ Q)
    (valid : ∀ A ⊆ G, ∀ q ∈ Q, pathArcs (choose A q) ⊆ G ∧
      (∀ path, choose A q = some path → Walk G q.1 q.2 path) ∧
      (Reach G q.1 q.2 → ∃ path, choose A q = some path)) :
    (∀ path, knownBudgetPath choose Q p F d = some path → Walk G d.1 d.2 path) ∧
      (Reach G d.1 d.2 → ∃ path, knownBudgetPath choose Q p F d = some path) := by
  let T := expensiveTrace choose p F p ∅ Q
  obtain ⟨_, _, hQ, _, _, _⟩ := expensiveTrace_spec choose p F p ∅ Q
  have hrun (A : Arcs V) (xs : List (V × V)) (ha : A ⊆ G) (hx : ∀ q ∈ xs, q ∈ Q) :
      runRule choose A xs ⊆ G := by
    induction xs generalizing A with
    | nil => exact ha
    | cons q qs ih =>
      refine ih (A ∪ pathArcs (choose A q)) ?_ (fun r hr => hx r (List.mem_cons_of_mem _ hr))
      exact union_subset ha (valid A ha q (hx q (List.mem_cons_self))).1
  obtain ⟨A, hs, he⟩ := assignedPath_uses_state choose ∅ T d
  change knownBudgetPath choose Q p F d = choose A d at he
  rw [he]
  exact (valid A (hs.trans (hrun ∅ T (empty_subset _) hQ)) d hd).2

end OnlineReachabilityPreservers
