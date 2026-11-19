import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.Connectors
import OnlineReachabilityPreservers.Restricted

/-! Theorem 9 and the general-digraph forms of Theorem 2. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [LinearOrder V] [Fintype V]

private def crossingCandidates (G : Arcs V) (e : V × V) : Finset (Lex (V × V)) :=
  (G.filter (fun a => projectDemand G a = e)).image toLex

/-- The unique deterministically chosen representative, when a preimage exists. -/
private def liftOne (G : Arcs V) (e : V × V) : Arcs V :=
  match least? (crossingCandidates G e) with
  | some a => {ofLex a}
  | none => ∅

private theorem liftOne_spec {G : Arcs V} {e a : V × V} (ha : a ∈ liftOne G e) :
    a ∈ G ∧ projectDemand G a = e := by
  unfold liftOne at ha
  split at ha
  · rename_i b hb
    have he := mem_singleton.mp ha
    obtain ⟨c, hc, rfl⟩ := mem_image.mp (least?_mem hb)
    subst a
    exact mem_filter.mp hc
  · simp at ha

private theorem liftOne_card (G : Arcs V) (e : V × V) : (liftOne G e).card ≤ 1 := by
  unfold liftOne
  split <;> simp

private theorem liftOne_some {G : Arcs V} {a b : V} (h : Edge (condensation G) a b) :
    ∃ e ∈ liftOne G (a, b), componentLabel G e.1 = a ∧ componentLabel G e.2 = b := by
  obtain ⟨_, u, v, edge, hu, hv⟩ := edge_condensation.mp h
  have hc : toLex (u, v) ∈ crossingCandidates G (a, b) :=
    mem_image.mpr ⟨(u, v), mem_filter.mpr ⟨edge, Prod.ext hu hv⟩, rfl⟩
  obtain ⟨c, hmin⟩ := least?_some ⟨_, hc⟩
  have he : ofLex c ∈ liftOne G (a, b) := by simp [liftOne, hmin]
  exact ⟨ofLex c, he, Prod.mk.inj (liftOne_spec he).2⟩

def liftedArcs (G H : Arcs V) : Arcs V := H.biUnion (liftOne G)

theorem liftedArcs_subset (G H : Arcs V) : liftedArcs G H ⊆ G := by
  intro e he
  obtain ⟨_, _, hl⟩ := mem_biUnion.mp he
  exact (liftOne_spec hl).1

theorem liftedArcs_mono (G : Arcs V) : Monotone (liftedArcs G) := by
  intro H K hk e he
  obtain ⟨a, ha, hl⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨a, hk ha, hl⟩

theorem liftedArcs_card (G H : Arcs V) : (liftedArcs G H).card ≤ H.card := by
  calc
    _ ≤ ∑ e ∈ H, (liftOne G e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ H, 1 := sum_le_sum (fun e _ => liftOne_card G e)
    _ = _ := by simp

theorem lift_selected_reach {G H : Arcs V} (sub : H ⊆ condensation G)
    {a b : V} (walk : Reach H a b) :
    ∀ u v, componentLabel G u = a → componentLabel G v = b →
      Reach (connectors G ∪ liftedArcs G H) u v := by
  induction walk with
  | refl =>
    intro u v hu hv
    exact reach_mono subset_union_left (connectors_reach (hu.trans hv.symm))
  | @tail x y _ he ih =>
    intro u v hu hv
    obtain ⟨e, hem, hx, hy⟩ := liftOne_some (sub he)
    have pre := ih u e.1 hu hx
    have mid : Edge (connectors G ∪ liftedArcs G H) e.1 e.2 :=
      mem_union_right _ (mem_biUnion.mpr ⟨(x, y), he, hem⟩)
    have post := reach_mono (G := connectors G ∪ liftedArcs G H) subset_union_left
      (connectors_reach (hy.trans hv.symm))
    exact (pre.tail mid).trans post

/-- Condense the input, apply the DAG algorithm to each revealed prefix, and lift its arcs.
The fixed internal connectors are added at the first request. -/
def liftedRun (run : Arcs V → List (V × V) → Arcs V) (G : Arcs V) (D : List (V × V)) : Arcs V :=
  match D with
  | [] => ∅
  | _ :: _ => connectors G ∪ liftedArcs G (run (condensation G) (D.map (projectDemand G)))

theorem liftedRun_prefix (run : Arcs V → List (V × V) → Arcs V)
    (online : ∀ G, IsDAG G → ∀ {P Q}, P <+: Q → run G P ⊆ run G Q)
    (G : Arcs V) {D E : List (V × V)} (h : D <+: E) :
    liftedRun run G D ⊆ liftedRun run G E := by
  cases D with
  | nil => exact empty_subset _
  | cons d ds =>
    cases E with
    | nil => simp at h
    | cons e es =>
      apply union_subset_union_right
      exact liftedArcs_mono G (online (condensation G) (condensation_dag G) (h.map _))

/-- Online form of the SCC reduction, with its exact finite overhead. -/
theorem theorem9_lift (run : Arcs V → List (V × V) → Arcs V)
    (G : Arcs V) (D : List (V × V))
    (sub : ∀ K, IsDAG K → ∀ P, run K P ⊆ K)
    (correct : ∀ K, IsDAG K → ∀ P, Preserves K (run K P) P) :
    liftedRun run G D ⊆ G ∧ Preserves G (liftedRun run G D) D ∧
      (liftedRun run G D).card ≤ (run (condensation G) (D.map (projectDemand G))).card +
        2 * Fintype.card V := by
  cases D with
  | nil => simp [liftedRun, Preserves]
  | cons d ds =>
    let P := (d :: ds).map (projectDemand G)
    let H := run (condensation G) P
    have hs : connectors G ∪ liftedArcs G H ⊆ G :=
      union_subset (connectors_subset G) (liftedArcs_subset G H)
    refine ⟨hs, ?_, ?_⟩
    · intro e he
      refine ⟨reach_mono hs, fun r => ?_⟩
      have hP : projectDemand G e ∈ P := List.mem_map.mpr ⟨e, he, rfl⟩
      have hr := (correct _ (condensation_dag G) P _ hP).mpr (project_reach r)
      exact lift_selected_reach (sub _ (condensation_dag G) P) hr e.1 e.2 rfl rfl
    · change (connectors G ∪ liftedArcs G H).card ≤ H.card + 2 * Fintype.card V
      have h₁ := connectors_card G
      have h₂ := liftedArcs_card G H
      have h₃ := card_union_le (connectors G) (liftedArcs G H)
      omega

private theorem eraseDups_sublist_nodup {A : Type*} [BEq A] [LawfulBEq A] (D : List A) :
    List.Sublist D.eraseDups D ∧ D.eraseDups.Nodup := by
  cases D with
  | nil => simp
  | cons d rest =>
    rw [List.eraseDups_cons]
    let remaining := rest.filter fun a => !a == d
    have cut : List.Sublist remaining rest := List.filter_sublist
    obtain ⟨sub,unique⟩ := eraseDups_sublist_nodup remaining
    refine ⟨List.Sublist.cons_cons d (sub.trans cut), List.nodup_cons.mpr ⟨?_,unique⟩⟩
    simp
termination_by D.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem eraseDups_prefix {A : Type*} [BEq A] [LawfulBEq A] {D E : List A} (hprefix : D <+: E) :
    D.eraseDups <+: E.eraseDups := by
  obtain ⟨extra,rfl⟩ := hprefix
  rw [List.eraseDups_append]
  exact List.prefix_append _ _

/-- Process projected demands in first-occurrence order and skip repetitions. -/
def projectedDistinctDemands (G : Arcs V) (D : List (V × V)) : List (V × V) :=
  (D.map (projectDemand G)).eraseDups

theorem projectedDistinctDemands_nodup (G : Arcs V) (D : List (V × V)) :
    (projectedDistinctDemands G D).Nodup :=
  (eraseDups_sublist_nodup (D.map (projectDemand G))).2

theorem projectedDistinctDemands_length_le (G : Arcs V) (D : List (V × V)) :
    (projectedDistinctDemands G D).length ≤ D.length := by
  simpa only [projectedDistinctDemands, List.length_map] using
    (eraseDups_sublist_nodup (D.map (projectDemand G))).1.length_le

/-- Contracting and deduplicating does not increase the number of distinct endpoints. -/
theorem projectedDistinctDemands_endpoints_le (G : Arcs V) (D : List (V × V)) (endpoint : V × V → V)
    (compatible : ∀ d, endpoint (projectDemand G d) = componentLabel G (endpoint d)) :
    ((projectedDistinctDemands G D).toFinset.image endpoint).card ≤ (D.toFinset.image endpoint).card := by
  have inclusion : (projectedDistinctDemands G D).toFinset.image endpoint ⊆
      (D.toFinset.image endpoint).image (componentLabel G) := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := mem_image.mp hw
    have before := List.mem_eraseDups.mp (List.mem_toFinset.mp he)
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp before
    exact mem_image.mpr ⟨endpoint d,mem_image.mpr ⟨d,List.mem_toFinset.mpr hd,rfl⟩,(compatible d).symm⟩
  exact (card_le_card inclusion).trans card_image_le

/-- Lift a DAG algorithm whose contract applies only to lists of distinct demands. -/
def liftedDistinctRun (run : Arcs V → List (V × V) → Arcs V) (G : Arcs V) (D : List (V × V)) : Arcs V :=
  liftedRun (fun K P => run K P.eraseDups) G D

theorem liftedDistinctRun_prefix (run : Arcs V → List (V × V) → Arcs V)
    (online : ∀ G, IsDAG G → ∀ {P Q}, P.Nodup → Q.Nodup → P <+: Q → run G P ⊆ run G Q)
    (G : Arcs V) {D E : List (V × V)} (hprefix : D <+: E) :
    liftedDistinctRun run G D ⊆ liftedDistinctRun run G E :=
  liftedRun_prefix (fun K P => run K P.eraseDups)
    (fun K dag {P Q} h => online K dag (eraseDups_sublist_nodup P).2 (eraseDups_sublist_nodup Q).2
      (eraseDups_prefix h)) G hprefix

/-- The SCC reduction with distinct DAG requests, preserving every original request. -/
theorem theorem9_lift_distinct (run : Arcs V → List (V × V) → Arcs V)
    (G : Arcs V) (D : List (V × V))
    (sub : ∀ K, IsDAG K → ∀ P, P.Nodup → run K P ⊆ K)
    (correct : ∀ K, IsDAG K → ∀ P, P.Nodup → Preserves K (run K P) P) :
    liftedDistinctRun run G D ⊆ G ∧ Preserves G (liftedDistinctRun run G D) D ∧
      (liftedDistinctRun run G D).card ≤ (run (condensation G) (projectedDistinctDemands G D)).card +
        2 * Fintype.card V := by
  apply theorem9_lift (fun K P => run K P.eraseDups) G D
  · exact fun K dag P => sub K dag _ (eraseDups_sublist_nodup P).2
  · intro K dag P e he
    exact (correct K dag _ (eraseDups_sublist_nodup P).2) e (List.mem_eraseDups.mpr he)

/-- The edge-budget form of Theorem 9 when the DAG bound is monotone in the
number of demands and the number of source or sink labels. -/
theorem theorem9_distinct_monotone_bound (run : Arcs V → List (V × V) → Arcs V)
    (G : Arcs V) (D : List (V × V)) (endpoint : V × V → V) (f : ℕ → ℕ → ℕ → ℕ)
    (compatible : ∀ d, endpoint (projectDemand G d) = componentLabel G (endpoint d))
    (sub : ∀ K, IsDAG K → ∀ P, P.Nodup → run K P ⊆ K)
    (correct : ∀ K, IsDAG K → ∀ P, P.Nodup → Preserves K (run K P) P)
    (size : ∀ K, IsDAG K → ∀ P, P.Nodup →
      (run K P).card ≤ f (Fintype.card V) P.length (P.toFinset.image endpoint).card)
    (mono : ∀ {p q s t}, p ≤ q → s ≤ t → f (Fintype.card V) p s ≤ f (Fintype.card V) q t) :
    liftedDistinctRun run G D ⊆ G ∧ Preserves G (liftedDistinctRun run G D) D ∧
      (liftedDistinctRun run G D).card ≤ f (Fintype.card V) D.length (D.toFinset.image endpoint).card +
        2*Fintype.card V := by
  obtain ⟨isSub, good, budget⟩ := theorem9_lift_distinct run G D sub correct
  have contracted := size (condensation G) (condensation_dag G) _ (projectedDistinctDemands_nodup G D)
  have stillFits := mono (projectedDistinctDemands_length_le G D)
    (projectedDistinctDemands_endpoints_le G D endpoint compatible)
  exact ⟨isSub, good, budget.trans (Nat.add_le_add_right (contracted.trans stillFits) _)⟩

/-- The sink-restricted online algorithm on an arbitrary directed graph. -/
def sinkPreserver (G : Arcs V) (D : List (V × V)) : Arcs V := liftedRun forwardRun G D

theorem sinkPreserver_prefix (G : Arcs V) {D E : List (V × V)} (h : D <+: E) :
    sinkPreserver G D ⊆ sinkPreserver G E :=
  liftedRun_prefix forwardRun (fun K _ => forwardRun_prefix K) G h

theorem sinkPreserver_spec (G : Arcs V) (D : List (V × V)) :
    sinkPreserver G D ⊆ G ∧ Preserves G (sinkPreserver G D) D ∧
      (sinkPreserver G D).card ≤ (forwardRun (condensation G) (D.map (projectDemand G))).card +
        2 * Fintype.card V :=
  theorem9_lift forwardRun G D (fun _ _ P => forwardRunFrom_subset (empty_subset _) P)
    (fun _ => forwardRun_preserves)

/-- On a DAG, the lifted preserver still pays for every edge bought by the
forward-growth run. This transfers its edge bounds to a quotient path rule. -/
theorem forwardRun_card_le_sinkPreserver {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    (forwardRun G D).card ≤ (sinkPreserver G D).card := by
  have label (v : V) : componentLabel G v = v := by
    have h := componentLabel_same (G := G) v
    rcases h.1.cases_tail with eq | ⟨x, vx, edge⟩
    · exact eq
    · exact (dag edge (h.2.trans vx)).elim
  have project : projectDemand G = id := by
    funext d
    exact Prod.ext (label d.1) (label d.2)
  have collapse : condensation G = G := by
    ext ⟨a,b⟩
    change Edge (condensation G) a b ↔ Edge G a b
    rw [edge_condensation]
    simp only [label]
    constructor
    · rintro ⟨_, u, v, uv, rfl, rfl⟩
      exact uv
    · intro ab
      refine ⟨?_, a, b, ab, rfl, rfl⟩
      rintro rfl
      exact dag ab .refl
  cases D with
  | nil => simp [sinkPreserver, liftedRun, forwardRun, forwardRunFrom]
  | cons d ds =>
    let H := forwardRun G (d :: ds)
    have sub : H ⊆ condensation G := collapse.symm ▸ forwardRunFrom_subset (empty_subset _) _
    have imageSub : H ⊆ (liftedArcs G H).image (projectDemand G) := by
      intro e he
      obtain ⟨a, ha, _, _⟩ := liftOne_some (sub he)
      exact mem_image.mpr ⟨a, mem_biUnion.mpr ⟨e, he, ha⟩, (liftOne_spec ha).2⟩
    have count := (card_le_card imageSub).trans card_image_le
    simpa only [sinkPreserver, liftedRun, collapse, project, List.map_id] using
      count.trans (card_le_card (subset_union_right : liftedArcs G H ⊆ _))

/-- The finite sink-restricted bound of Theorem 2, on every prefix of a demand trace. -/
theorem theorem2_sinks (G : Arcs V) (D : List (V × V)) (S : Finset V)
    (sinks : ∀ d ∈ D, d.2 ∈ S) :
    sinkPreserver G D ⊆ G ∧ Preserves G (sinkPreserver G D) D ∧
      ((sinkPreserver G D).card : ℝ) ≤
        3 * Fintype.card V + Real.sqrt (2 * Fintype.card V * D.length * S.card) := by
  obtain ⟨hs, hp, hcard⟩ := sinkPreserver_spec G D
  have ⟨_, hb⟩ := theorem11_sinks (condensation_dag G) (D.map (projectDemand G))
    (S.image (componentLabel G)) (by
      intro e he
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      exact mem_image.mpr ⟨d.2, sinks d hd, rfl⟩)
  have himage : ((S.image (componentLabel G)).card : ℝ) ≤ S.card := by exact_mod_cast card_image_le
  have hl : (((D.map (projectDemand G)).length : ℕ) : ℝ) = D.length := by simp
  have hbudget : ((sinkPreserver G D).card : ℝ) ≤
      (forwardRun (condensation G) (D.map (projectDemand G))).card + 2 * Fintype.card V := by
    exact_mod_cast hcard
  refine ⟨hs, hp, ?_⟩
  rw [hl] at hb
  have hr : Real.sqrt (2 * Fintype.card V * D.length * (S.image (componentLabel G)).card) ≤
      Real.sqrt (2 * Fintype.card V * D.length * S.card) := by
    apply Real.sqrt_le_sqrt
    gcongr
  linarith

/-- The source-restricted algorithm uses the same construction in the opposite orientation. -/
def sourcePreserver (G : Arcs V) (D : List (V × V)) : Arcs V :=
  reverseArcs (sinkPreserver (reverseArcs G) (D.map Prod.swap))

theorem sourcePreserver_prefix (G : Arcs V) {D E : List (V × V)} (h : D <+: E) :
    sourcePreserver G D ⊆ sourcePreserver G E :=
  reverseArcs_mono (sinkPreserver_prefix _ (h.map _))

/-- The finite source-restricted bound of Theorem 2 on arbitrary digraphs. -/
theorem theorem2_sources (G : Arcs V) (D : List (V × V)) (S : Finset V)
    (sources : ∀ d ∈ D, d.1 ∈ S) :
    sourcePreserver G D ⊆ G ∧ Preserves G (sourcePreserver G D) D ∧
      ((sourcePreserver G D).card : ℝ) ≤
        3 * Fintype.card V + Real.sqrt (2 * Fintype.card V * D.length * S.card) := by
  obtain ⟨hs, hp, hb⟩ := theorem2_sinks (reverseArcs G) (D.map Prod.swap) S (by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact sources d hd)
  refine ⟨by simpa [sourcePreserver] using reverseArcs_mono hs, ?_,
    by simpa [sourcePreserver] using hb⟩
  intro d hd
  rw [sourcePreserver, reach_reverseArcs]
  exact (hp d.swap (List.mem_map.mpr ⟨d, hd, rfl⟩)).trans reach_reverseArcs

end OnlineReachabilityPreservers
