import Mathlib.Algebra.Order.BigOperators.Expect
import OnlineReachabilityPreservers.SteinerCompetitive
import OnlineReachabilityPreservers.SteinerEarlyRound
import OnlineReachabilityPreservers.SteinerRate

/-! Combine early rounding with the hub and thin routines using a fixed
list of distinct non-self arrivals. -/

namespace OnlineReachabilityPreservers

universe u

open Finset
open scoped BigOperators

variable {V : Type*} [LinearOrder V] [Fintype V]

private def keepNewNonself (seen : List (V × V)) (d : V × V) : List (V × V) :=
  if d.1 = d.2 ∨ d ∈ seen then seen else seen ++ [d]

/-- First occurrences of non-self requests, in arrival order. -/
def distinctNonselfTrace (D : List (V × V)) : List (V × V) :=
  D.foldl keepNewNonself []

omit [Fintype V] in
private theorem distinctNonselfTrace_snoc (D : List (V × V)) (d : V × V) :
    distinctNonselfTrace (D ++ [d]) = keepNewNonself (distinctNonselfTrace D) d := by
  simp [distinctNonselfTrace]

omit [Fintype V] in
theorem mem_distinctNonselfTrace {D : List (V × V)} {d : V × V} :
    d ∈ distinctNonselfTrace D ↔ d ∈ D ∧ d.1 ≠ d.2 := by
  induction D using List.reverseRecOn generalizing d with
  | nil => simp [distinctNonselfTrace]
  | append_singleton D next ih =>
    rw [distinctNonselfTrace_snoc]
    by_cases skip : next.1 = next.2 ∨ next ∈ distinctNonselfTrace D
    · simp only [keepNewNonself, skip, ↓reduceIte]
      simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · exact fun h => ⟨Or.inl h.1, h.2⟩
      · rintro ⟨inside | equal, nonself⟩
        · exact ⟨inside, nonself⟩
        · subst d
          rcases skip with self | seen
          · exact (nonself self).elim
          · exact (ih (d := next)).mp seen
    · have nonself : next.1 ≠ next.2 := fun eq => skip (Or.inl eq)
      simp only [keepNewNonself, skip, ↓reduceIte]
      simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨inside, no⟩ | equal)
        · exact ⟨Or.inl inside, no⟩
        · subst d
          exact ⟨Or.inr rfl, nonself⟩
      · rintro ⟨inside | equal, no⟩
        · exact Or.inl ⟨inside, no⟩
        · exact Or.inr equal

omit [Fintype V] in
theorem distinctNonselfTrace_nodup (D : List (V × V)) : (distinctNonselfTrace D).Nodup := by
  induction D using List.reverseRecOn with
  | nil => simp [distinctNonselfTrace]
  | append_singleton D next ih =>
    rw [distinctNonselfTrace_snoc]
    unfold keepNewNonself
    split
    · exact ih
    · rename_i keep
      apply List.nodup_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro a ha b only same
      exact keep (Or.inr ((same.trans (List.mem_singleton.mp only)) ▸ ha))

omit [Fintype V] in
theorem distinctNonselfTrace_prefix {D E : List (V × V)} (pref : D <+: E) :
    distinctNonselfTrace D <+: distinctNonselfTrace E := by
  obtain ⟨T, rfl⟩ := pref
  induction T using List.reverseRecOn with
  | nil => simp
  | append_singleton T next ih =>
    rw [← List.append_assoc, distinctNonselfTrace_snoc]
    apply ih.trans
    unfold keepNewNonself
    split
    · exact List.prefix_rfl
    · exact List.prefix_append _ _

private def lateUnusedRule (G : Arcs V) : EarlySteinerRule G where
  run D := if D = [] then ∅ else G
  empty := by simp
  subset D := by split <;> simp
  online := by
    intro D E prefixOf
    by_cases eq : E = []
    · have same : D = [] := List.prefix_nil.mp (eq ▸ prefixOf)
      simp [eq, same]
    · simp only [eq, ↓reduceIte]
      split <;> simp
  preserves := by
    intro D _ d member
    have ne : D ≠ [] := by rintro rfl; simp at member
    simp [ne]

/-- The split depends only on the arrivals. The late algorithm starts
with its early cutoff set to zero because early rounding has already
processed the first block of distinct non-self pairs. -/
def completeSteinerRun (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (hubs : Finset V) (thin : ThinSample G) (D : List (V × V)) : Arcs V :=
  let n := Fintype.card V
  let T := steinerEarlyCutoff n
  let P := distinctNonselfTrace D
  earlyRoundedGraph G height (P.take T) early ∪
    assembledSteiner (lateUnusedRule G) 0 (steinerThinThreshold n) hubs thin (P.drop T)

theorem completeSteinerRun_empty (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (hubs : Finset V) (thin : ThinSample G) :
    completeSteinerRun G height early hubs thin [] = ∅ := by
  simp [completeSteinerRun, distinctNonselfTrace, earlyRoundedGraph_empty, assembledSteiner_empty]

theorem completeSteinerRun_prefix (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (hubs : Finset V) (thin : ThinSample G) {D E : List (V × V)} (prefixOf : D <+: E)
    (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    completeSteinerRun G height early hubs thin D ⊆ completeSteinerRun G height early hubs thin E := by
  have pref := distinctNonselfTrace_prefix prefixOf
  exact union_subset_union (earlyRoundedGraph_mono G height early (pref.take _))
    (assembledSteiner_prefix (lateUnusedRule G) 0 _ hubs thin (pref.drop _)
      (fun d hd => feasible d (mem_distinctNonselfTrace.mp (List.mem_of_mem_drop hd)).1))

theorem completeSteinerRun_correct (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (hubs : Finset V) (thin : ThinSample G) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    completeSteinerRun G height early hubs thin D ⊆ G ∧
      Preserves G (completeSteinerRun G height early hubs thin D) D := by
  let n := Fintype.card V
  let T := steinerEarlyCutoff n
  let P := distinctNonselfTrace D
  let left := earlyRoundedGraph G height (P.take T) early
  let right := assembledSteiner (lateUnusedRule G) 0 (steinerThinThreshold n) hubs thin (P.drop T)
  have leftSub := earlyRoundedGraph_sub G height (P.take T) early
  obtain ⟨rightSub, rightOk⟩ := assembledSteiner_correct (lateUnusedRule G) 0
    (steinerThinThreshold n) hubs thin (P.drop T)
    (fun d hd => feasible d (mem_distinctNonselfTrace.mp (List.mem_of_mem_drop hd)).1)
  have sub : left ∪ right ⊆ G := union_subset leftSub rightSub
  refine ⟨sub, fun d hd => ⟨reach_mono sub, fun path => ?_⟩⟩
  by_cases self : d.1 = d.2
  · exact self ▸ Relation.ReflTransGen.refl
  have present : d ∈ P := mem_distinctNonselfTrace.mpr ⟨hd, self⟩
  have split : d ∈ P.take T ∨ d ∈ P.drop T := List.mem_append.mp ((List.take_append_drop T P).symm ▸ present)
  rcases split with elected | later
  · exact reach_mono (subset_union_left (s₁ := left) (s₂ := right))
      ((earlyRoundedGraph_preserves G height (P.take T) early d elected).mpr path)
  · exact reach_mono (subset_union_right (s₁ := left) (s₂ := right)) ((rightOk d later).mpr path)

private theorem completeSteiner_late_opt {Z : Arcs V} (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (existsLate : (distinctNonselfTrace D).drop (steinerEarlyCutoff (Fintype.card V)) ≠ []) :
    steinerEarlyCutoff (Fintype.card V) ≤ Z.card ^ 2 := by
  let P := distinctNonselfTrace D
  let T := steinerEarlyCutoff (Fintype.card V)
  have reachesCutoff : T ≤ P.length := by
    by_contra! short
    have len : (P.drop T).length = 0 := by rw [List.length_drop]; omega
    exact existsLate (List.length_eq_zero_iff.mp len)
  apply reachesCutoff.trans
  rw [← List.toFinset_card_of_nodup (distinctNonselfTrace_nodup D)]
  exact lemma20_opt_squared P.toFinset Z
    (fun d hd => (mem_distinctNonselfTrace.mp (List.mem_toFinset.mp hd)).2)
    (fun d hd => feasible d (mem_distinctNonselfTrace.mp (List.mem_toFinset.mp hd)).1)

/-- The sample size of the executable integer hub budget. -/
def completeSteinerHubCount (V : Type*) [Fintype V] : ℕ :=
  steinerHubDraws (Fintype.card V) (steinerThinThreshold (Fintype.card V))

theorem completeSteinerHubCount_empty (V : Type*) [Fintype V] [IsEmpty V] :
    completeSteinerHubCount V = 0 := by
  simp [completeSteinerHubCount, steinerHubDraws]

theorem completeSteinerHubDraw_empty (V : Type*) [Fintype V] [IsEmpty V] :
    Nonempty (Fin (completeSteinerHubCount V) → V) := by
  rw [completeSteinerHubCount_empty]
  exact ⟨Fin.elim0⟩

def completeSteinerDrawRun (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V)) : Arcs V :=
  completeSteinerRun G height early (sampledVertices draw) thin D

theorem completeSteinerDrawRun_correct (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    completeSteinerDrawRun G height early draw thin D ⊆ G ∧
      Preserves G (completeSteinerDrawRun G height early draw thin D) D :=
  completeSteinerRun_correct G height early (sampledVertices draw) thin D feasible

theorem completeSteinerDrawRun_prefix (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) {D E : List (V × V)}
    (prefixOf : D <+: E) (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    completeSteinerDrawRun G height early draw thin D ⊆ completeSteinerDrawRun G height early draw thin E :=
  completeSteinerRun_prefix G height early (sampledVertices draw) thin prefixOf feasible

/-- Independent finite early, hub, and thin draws. -/
noncomputable def completeSteinerMean (G : Arcs V) (height : ℕ) (D : List (V × V)) : ℝ :=
  let n := Fintype.card V
  let k := completeSteinerHubCount V
  𝔼 sample : EarlyRoundSample G height,
    ((∑ draw : Fin k → V, thinMean G (fun thin =>
      completeSteinerDrawRun G height sample draw thin D)) / (n : ℝ) ^ k)

private theorem completeSteinerMean_le_split [Nonempty V] (G : Arcs V)
    (height : ℕ) (D : List (V × V)) :
    let n := Fintype.card V
    let T := steinerEarlyCutoff n
    let P := distinctNonselfTrace D
    (completeSteinerMean G height D) ≤
      (𝔼 sample : EarlyRoundSample G height, ((earlyRoundedGraph G height (P.take T) sample).card : ℝ)) +
      assembledSteinerMeanOfDrawCount (lateUnusedRule G) 0 (steinerThinThreshold n)
        (completeSteinerHubCount V) (P.drop T) := by
  classical
  let n := Fintype.card V
  let T := steinerEarlyCutoff n
  let τ := steinerThinThreshold n
  let k := completeSteinerHubCount V
  let P := distinctNonselfTrace D
  let q := (n : ℝ) ^ k
  let late := assembledSteinerMeanOfDrawCount (lateUnusedRule G) 0 τ k (P.drop T)
  let first := fun sample : EarlyRoundSample G height => ((earlyRoundedGraph G height (P.take T) sample).card : ℝ)
  let middle := fun (draw : Fin k → V) => thinMean G (fun thin =>
    assembledSteiner (lateUnusedRule G) 0 τ (sampledVertices draw) thin (P.drop T))
  let combined := fun sample : EarlyRoundSample G height =>
    (∑ draw : Fin k → V, thinMean G (fun thin =>
      completeSteinerRun G height sample (sampledVertices draw) thin D)) / q
  have qPos : 0 < q := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  have card : (Fintype.card (Fin k → V) : ℝ) = q := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have point (sample : EarlyRoundSample G height) : combined sample ≤ first sample + late := by
    calc
      _ ≤ (∑ draw : Fin k → V, (first sample + middle draw)) / q := by
        apply div_le_div_of_nonneg_right _ qPos.le
        apply sum_le_sum
        intro draw _
        exact thinMean_union_const G (earlyRoundedGraph G height (P.take T) sample)
          (fun thin => assembledSteiner (lateUnusedRule G) 0 τ (sampledVertices draw) thin (P.drop T))
      _ = _ := by
        rw [sum_add_distrib, add_div, sum_const, nsmul_eq_mul, card_univ, card]
        rw [mul_comm q, mul_div_assoc, div_self qPos.ne', mul_one]
        rfl
  let bits : ℕ := forestSeedSize (forestScale G height)
  have bitsPos : 0 < bits := by dsimp [bits, forestSeedSize]; positivity
  let zero : Fin bits := ⟨0, bitsPos⟩
  have nonempty : Nonempty (EarlyRoundSample G height) :=
    ⟨fun _ _ _ => ⟨zero, fun _ _ => zero⟩⟩
  change (𝔼 sample : EarlyRoundSample G height, combined sample) ≤
    (𝔼 sample : EarlyRoundSample G height, first sample) + late
  calc
    _ ≤ (𝔼 sample : EarlyRoundSample G height, (first sample + late)) :=
      Finset.expect_le_expect (fun sample _ => point sample)
    _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]

private theorem completeSteiner_late_rate {ε : ℝ} (epsilon : 0 < ε) :
    ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] [Nonempty V] {G Z : Arcs V}
      (D : List (V × V)), 0 < Z.card → Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
      assembledSteinerMeanOfDrawCount (lateUnusedRule G) 0 (steinerThinThreshold (Fintype.card V))
        (completeSteinerHubCount V) ((distinctNonselfTrace D).drop (steinerEarlyCutoff (Fintype.card V))) ≤
        K * (Fintype.card V : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨K, pos, bound⟩ := assembledSteiner_late_rate_of_integer_draws.{u} epsilon
  refine ⟨K, pos, ?_⟩
  intro V _ _ _ G Z D Zpos sub feasible
  let Q := (distinctNonselfTrace D).drop (steinerEarlyCutoff (Fintype.card V))
  have req : ∀ d ∈ Q, Reach Z d.1 d.2 :=
    fun d hd => feasible d (mem_distinctNonselfTrace.mp (List.mem_of_mem_drop hd)).1
  have opt (S : Finset V) (hits : (steinerPhaseTraces (lateUnusedRule G) 0 S Q).hits ≠ []) :
      steinerEarlyCutoff (Fintype.card V) ≤ Z.card ^ 2 := by
    apply completeSteiner_late_opt D feasible
    intro no
    change Q = [] at no
    rw [no] at hits
    exact hits rfl
  have zero (S : Finset V) : ((lateUnusedRule G).run (steinerPhaseTraces (lateUnusedRule G) 0 S Q).early).card = 0 := by
    rw [steinerPhaseTraces_early_empty_at_zero, (lateUnusedRule G).empty, card_empty]
  have full := bound V (lateUnusedRule G) 0 Q 0 le_rfl Fintype.card_pos Zpos sub req opt
    (fun S => by rw [zero, Nat.cast_zero])
  simpa only [zero_add, completeSteinerHubCount, Q] using full

private theorem completeSteinerMean_zero_of_no_nonself (G : Arcs V)
    (height : ℕ) (D : List (V × V)) (none : distinctNonselfTrace D = []) :
    completeSteinerMean G height D = 0 := by
  have empty (sample : EarlyRoundSample G height) (hubs : Finset V) (thin : ThinSample G) :
      completeSteinerRun G height sample hubs thin D = ∅ := by
    simp [completeSteinerRun, none, earlyRoundedGraph_empty, assembledSteiner_empty]
  simp [completeSteinerMean, completeSteinerDrawRun, empty, thinMean]

omit [LinearOrder V] [Fintype V] in
private theorem reach_empty_eq {s t : V} (path : Reach (∅ : Arcs V) s t) : s = t := by
  cases path with
  | refl => rfl
  | tail _ edge => exact (notMem_empty _ edge).elim

/-- The expected competitive edge bound of Theorems 8 and 21 on a fixed
feasible demand sequence. The output is the executable immutable-prefix
algorithm `completeSteinerDrawRun`, for which correctness holds on every seed. -/
theorem theorem21_online_steiner_expected {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [LinearOrder V] [Fintype V] {G Z : Arcs V}
        (D : List (V × V)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        completeSteinerMean G height D ≤ K * (Fintype.card V : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨height, heightPos, A, Apos, early⟩ := earlyRoundedGraph_rate.{u} epsilon
  obtain ⟨B, Bpos, late⟩ := completeSteiner_late_rate.{u} epsilon
  refine ⟨height, heightPos, A + B, add_pos Apos Bpos, ?_⟩
  intro V _ _ G Z D sub feasible
  by_cases zero : Z = ∅
  · have none : distinctNonselfTrace D = [] := by
      cases trace : distinctNonselfTrace D with
      | nil => rfl
      | cons d rest =>
        have member : d ∈ distinctNonselfTrace D := by rw [trace]; exact List.mem_cons_self
        obtain ⟨input, nonself⟩ := mem_distinctNonselfTrace.mp member
        exact (nonself (reach_empty_eq (zero ▸ feasible d input))).elim
    rw [completeSteinerMean_zero_of_no_nonself G height D none, zero, card_empty, Nat.cast_zero, mul_zero]
  have positive : 0 < Z.card := card_pos.mpr (nonempty_iff_ne_empty.mpr zero)
  obtain ⟨edge, _⟩ := card_pos.mp positive
  have inhabited : Nonempty V := ⟨edge.1⟩
  let E := (distinctNonselfTrace D).take (steinerEarlyCutoff (Fintype.card V))
  have nodup : E.Nodup := (distinctNonselfTrace_nodup D).take
  have cap : E.length ≤ steinerEarlyCutoff (Fintype.card V) := by simp [E, List.length_take]
  have feasibleEarly : ∀ d ∈ E, Reach Z d.1 d.2 :=
    fun d hd => feasible d (mem_distinctNonselfTrace.mp (List.mem_of_mem_take hd)).1
  refine (completeSteinerMean_le_split G height D).trans ?_
  calc
    _ ≤ A * (Fintype.card V : ℝ) ^ (3/5 + ε) * Z.card +
        B * (Fintype.card V : ℝ) ^ (3/5 + ε) * Z.card :=
      add_le_add (early V E nodup cap positive sub feasibleEarly) (late V D positive sub feasible)
    _ = _ := by ring

end OnlineReachabilityPreservers
