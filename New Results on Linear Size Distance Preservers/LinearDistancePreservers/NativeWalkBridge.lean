import LinearDistancePreservers.RoutingOfPaths
import LinearDistancePreservers.PathUnion

/-! Exact correspondence between mathlib's walk datatype and the package's
list-walk distances. The complete ambient graph does not change which
directed steps are allowed. Self-loops can be erased without increasing cost. -/
namespace LinearDistancePreservers.ConsistentTiebreaking
open SimpleGraph WeightedDigraph
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {K : SimpleGraph V}

theorem zip_support {s t : V} (p : K.Walk s t) :
    p.support.zip p.support.tail = p.darts.map Dart.toProd := by
  induction p with
  | nil => simp
  | @cons s u t h p ih =>
    rw [Walk.support_cons, List.tail_cons, Walk.darts_cons, List.map_cons]
    nth_rw 2 [← p.cons_tail_support]
    rw [List.zip_cons_cons]
    exact congrArg (fun l => (s,u) :: l) ih

theorem support_isWalk {G : V → V → Prop} {s t : V} {p : K.Walk s t}
    (hp : Allowed G p) : IsWalk G s t p.support := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.head?_eq_some_head p.support_ne_nil, Walk.head_support]
  · rw [List.getLast?_eq_some_getLast p.support_ne_nil, Walk.getLast_support]
  · intro e he
    rw [zip_support] at he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact hp d hd

theorem cost_cons_cons (w : V → V → ℝ≥0∞) (a b : V) (l : List V) :
    cost w (a :: b :: l) = w a b + cost w (b :: l) := rfl

theorem cost_cons_support (w : V → V → ℝ≥0∞) {s t : V}
    (a : V) (p : K.Walk s t) : cost w (a :: p.support) = w a s + cost w p.support := by
  rw [← p.cons_tail_support, cost_cons_cons]

theorem cost_support (w : V → V → ℝ≥0) {s t : V} (p : K.Walk s t) :
    cost (fun u v => (w u v : ℝ≥0∞)) p.support =
      ENNReal.ofReal ((p.darts.map fun d => (w d.fst d.snd : ℝ)).sum) := by
  induction p with
  | nil => simp [cost]
  | @cons s u t h p ih =>
    have hnon : 0 ≤ (p.darts.map fun d => (w d.fst d.snd : ℝ)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
      exact (w d.fst d.snd).coe_nonneg
    rw [Walk.support_cons, cost_cons_support, ih, Walk.darts_cons,
      List.map_cons, List.sum_cons, ENNReal.ofReal_add (w s u).coe_nonneg hnon]
    simp [ENNReal.ofReal_coe_nnreal]

/-- Convert every actual directed list walk into an allowed native walk.
The only discarded steps are self-loops, whose weights are nonnegative. -/
theorem exists_native_walk_le (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} {l : List V} (h : IsWalk G s t l) :
    ∃ p : (⊤ : SimpleGraph V).Walk s t, Allowed G p ∧
      cost (fun u v => (w u v : ℝ≥0∞)) p.support ≤ cost (fun u v => (w u v : ℝ≥0∞)) l := by
  induction l generalizing s with
  | nil => cases h.1
  | cons a l ih =>
    have ha : a = s := by simpa using h.1
    subst s
    cases l with
    | nil =>
      have ht : a = t := by simpa using h.2.1
      subst t
      exact ⟨.nil, by simp [Allowed], le_rfl⟩
    | cons b l =>
      have hab : G a b := h.2.2 (a,b) (by simp)
      have htail : IsWalk G b t (b :: l) := by
        refine ⟨rfl, ?_, ?_⟩
        · simpa using h.2.1
        · intro e he
          exact h.2.2 e (by simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr he)
      obtain ⟨p, hp, hle⟩ := ih htail
      by_cases heq : a = b
      · subst b
        refine ⟨p, hp, ?_⟩
        rw [cost_cons_cons]
        exact hle.trans (le_add_of_nonneg_left (by positivity))
      · have hedge : (⊤ : SimpleGraph V).Adj a b := heq
        refine ⟨.cons hedge p, ?_, ?_⟩
        · simpa [Allowed, Walk.darts_cons] using And.intro hab hp
        · rw [Walk.support_cons, cost_cons_support, cost_cons_cons]
          exact add_le_add (le_refl _) hle

/-- An optimal native path attains the original list-based graph distance. -/
theorem Optimal.attains_distance {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : (⊤ : SimpleGraph V).Walk s t} (hp : Optimal G w p) :
    cost (fun u v => (w u v : ℝ≥0∞)) p.support =
      distance G (fun u v => (w u v : ℝ≥0∞)) s t := by
  apply le_antisymm _ (distance_le_cost (support_isWalk hp.1))
  apply le_sInf
  rintro c ⟨l, hl, rfl⟩
  obtain ⟨q, hq, hle⟩ := exists_native_walk_le G w hl
  apply le_trans _ hle
  rw [cost_support, cost_support]
  exact ENNReal.ofReal_le_ofReal (hp.shortest q hq)

/-- The path union is exactly the edges of the extracted routing, with the
head/tail order reversed as required by the branching module. -/
theorem routing_edges_iff {G : V → V → Prop} {w : V → V → ℝ≥0}
    {I : Type*} [Fintype I] (s t : I → V)
    (p : ∀ i, (⊤ : SimpleGraph V).Walk (s i) (t i))
    (hp : ∀ i, Optimal G w (p i)) (u v : V) :
    PathUnion (fun i => (p i).support) u v ↔ (v,u) ∈ (routing s t p hp).edges := by
  classical
  simp only [Routing.edges, Finset.mem_filter, Finset.mem_univ, true_and,
    Routing.mem_tails, routing, PathUnion, predecessor_some_iff (hp _).2.1, zip_support,
    List.mem_map]
  constructor
  · rintro ⟨i, d, hd, he⟩
    exact ⟨i, d, hd, congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨i, d, hd, h1, h2⟩
    exact ⟨i, d, hd, Prod.ext h1 h2⟩

end LinearDistancePreservers.ConsistentTiebreaking
