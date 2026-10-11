import LinearDistancePreservers.ConsistentTiebreaking
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Tactic

/-! Actual finite directed, nonnegatively weighted graphs. An ambient simple
 graph provides the walk type; the Allowed relation independently orients its
 arcs. Distances are infima of actual directed walk costs, not supplied metrics. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped ENNReal NNReal
variable {V : Type*} [Fintype V] [DecidableEq V] {K : SimpleGraph V}
attribute [local instance] Classical.propDecidable

def edgeRel (F : Finset (V × V)) (u v : V) : Prop := (u,v) ∈ F

noncomputable def arcList {s t : V} (p : K.Walk s t) : List (V × V) :=
  p.darts.map fun d => (d.fst, d.snd)

noncomputable def arcs {s t : V} (p : K.Walk s t) : Finset (V × V) := (arcList p).toFinset

noncomputable def realCost (w : V → V → ℝ≥0) {s t : V} (p : K.Walk s t) : ℝ :=
  (p.darts.map fun d => (w d.fst d.snd : ℝ)).sum

noncomputable def cost (w : V → V → ℝ≥0) {s t : V} (p : K.Walk s t) : ℝ≥0∞ :=
  ENNReal.ofReal (realCost w p)

noncomputable def distance (K : SimpleGraph V) (A : V → V → Prop) (w : V → V → ℝ≥0)
    (s t : V) : ℝ≥0∞ := sInf {c | ∃ p : K.Walk s t, Allowed A p ∧ c = cost w p}

theorem realCost_nonneg (w : V → V → ℝ≥0) {s t : V} (p : K.Walk s t) : 0 ≤ realCost w p := by
  unfold realCost
  exact List.sum_nonneg (by intro x hx; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; exact (w d.fst d.snd).coe_nonneg)

theorem cost_append (w : V → V → ℝ≥0) {s r t : V} (p : K.Walk s r) (q : K.Walk r t) :
    cost w (p.append q) = cost w p + cost w q := by
  have hr : realCost w (p.append q) = realCost w p + realCost w q := by
    simp [realCost, Walk.darts_append]
  unfold cost
  rw [hr, ENNReal.ofReal_add (realCost_nonneg w p) (realCost_nonneg w q)]

theorem distance_le_cost {A : V → V → Prop} (w : V → V → ℝ≥0)
    {s t : V} (p : K.Walk s t) (hp : Allowed A p) : distance K A w s t ≤ cost w p :=
  sInf_le ⟨p, hp, rfl⟩

theorem distance_mono {A B : V → V → Prop} (w : V → V → ℝ≥0)
    (h : ∀ u v, A u v → B u v) (s t : V) : distance K B w s t ≤ distance K A w s t := by
  apply sInf_le_sInf
  rintro c ⟨p, hp, rfl⟩
  exact ⟨p, fun d hd => h _ _ (hp d hd), rfl⟩

theorem distance_eq_cost {A : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : K.Walk s t} (hp : Optimal A w p) : distance K A w s t = cost w p := by
  apply le_antisymm (distance_le_cost w p hp.1)
  apply le_sInf
  rintro c ⟨q, hq, rfl⟩
  exact ENNReal.ofReal_le_ofReal (hp.shortest q hq)

theorem distance_of_no_walk {A : V → V → Prop} (w : V → V → ℝ≥0) {s t : V}
    (h : ¬∃ p : K.Walk s t, Allowed A p) : distance K A w s t = ⊤ := by
  have he : {c | ∃ p : K.Walk s t, Allowed A p ∧ c = cost w p} = (∅ : Set ℝ≥0∞) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, _⟩
    exact h ⟨p, hp⟩
  simp [distance, he]

theorem distance_triangle (A : V → V → Prop) (w : V → V → ℝ≥0) (s r t : V) :
    distance K A w s t ≤ distance K A w s r + distance K A w r t := by
  by_cases hsr : ∃ p : K.Walk s r, Allowed A p
  · by_cases hrt : ∃ q : K.Walk r t, Allowed A q
    · obtain ⟨p, hp⟩ := exists_optimal A w s r hsr
      obtain ⟨q, hq⟩ := exists_optimal A w r t hrt
      rw [distance_eq_cost hp, distance_eq_cost hq, ← cost_append]
      exact distance_le_cost w (p.append q) ((allowed_append A p q).mpr ⟨hp.1,hq.1⟩)
    · simp [distance_of_no_walk w hrt]
  · simp [distance_of_no_walk w hsr]

theorem allowed_of_arcs {A : V → V → Prop} {s t : V} (p : K.Walk s t)
    (h : ∀ e ∈ arcs p, A e.1 e.2) : Allowed A p := by
  intro d hd
  exact h (d.fst,d.snd) (List.mem_toFinset.mpr (List.mem_map.mpr ⟨d,hd,rfl⟩))

theorem arcs_allowed {A : V → V → Prop} {s t : V} (p : K.Walk s t)
    (h : Allowed A p) {e : V × V} (he : e ∈ arcs p) : A e.1 e.2 := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  exact h d hd

theorem arcs_card_le {s t : V} (p : K.Walk s t) : (arcs p).card ≤ p.length := by
  exact List.toFinset_card_le.trans (by simp [arcList])

theorem cost_reverse (w : V → V → ℝ≥0) {s t : V} (p : K.Walk s t) :
    cost (fun u v => w v u) p.reverse = cost w p := by
  simp [cost, realCost, Walk.darts_reverse, List.map_map, Function.comp_def]

theorem allowed_reverse (A : V → V → Prop) {s t : V} (p : K.Walk s t) :
    Allowed (fun u v => A v u) p.reverse ↔ Allowed A p := by
  simp [Allowed, Walk.darts_reverse]

theorem distance_reverse (A : V → V → Prop) (w : V → V → ℝ≥0) (s t : V) :
    distance K (fun u v => A v u) (fun u v => w v u) t s = distance K A w s t := by
  unfold distance
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.reverse, (allowed_reverse (fun u v => A v u) p).mpr hp, ?_⟩
    exact (cost_reverse (fun u v => w v u) p).symm
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.reverse, (allowed_reverse A p).mpr hp, (cost_reverse w p).symm⟩

/-- Split a chosen optimal path at any vertex on it. -/
theorem distance_split {A : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} (p : K.Walk s t) (hp : Optimal A w p) (r : V) (hr : r ∈ p.support) :
    distance K A w s r + distance K A w r t = distance K A w s t := by
  rw [distance_eq_cost (hp.subwalk (p.isSubwalk_takeUntil hr)),
    distance_eq_cost (hp.subwalk (p.isSubwalk_dropUntil hr)), distance_eq_cost hp,
    ← cost_append, Walk.take_spec]

end SlackSparsification.Directed
