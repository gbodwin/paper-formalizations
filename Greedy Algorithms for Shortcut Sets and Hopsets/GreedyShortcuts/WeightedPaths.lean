import GreedyShortcuts.DirectedPaths

/-!
Weighted directed walks on the native complete-graph walk datatype. The input
relation is tested on every directed dart. Weights are nonnegative real numbers;
shortestness and uniqueness below quantify over all finite walks, not just paths.
-/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph
open GreedyShortcuts.DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cost (w : V → V → ℝ≥0) {s t : V} (p : DWalk s t) : ℝ :=
  (p.darts.map fun d => (w d.fst d.snd : ℝ)).sum

@[simp] theorem cost_nil (w : V → V → ℝ≥0) (s : V) :
    cost w (Walk.nil : DWalk s s) = 0 := by simp [cost]

@[simp] theorem cost_cons (w : V → V → ℝ≥0) {s u t : V}
    (h : (⊤ : SimpleGraph V).Adj s u) (p : DWalk u t) :
    cost w (Walk.cons h p) = (w s u : ℝ) + cost w p := by simp [cost]

theorem cost_append (w : V → V → ℝ≥0) {s u t : V}
    (p : DWalk s u) (q : DWalk u t) :
    cost w (p.append q) = cost w p + cost w q := by
  simp [cost, Walk.darts_append]

theorem cost_nonneg (w : V → V → ℝ≥0) {s t : V} (p : DWalk s t) :
    0 ≤ cost w p := by
  induction p with
  | nil => simp
  | cons h p ih => exact add_nonneg (w _ _).coe_nonneg ih

theorem cost_add_scale (w₀ w₁ : V → V → ℝ≥0) (δ : ℝ≥0)
    {s t : V} (p : DWalk s t) :
    cost (fun u v => w₀ u v + δ * w₁ u v) p =
      cost w₀ p + (δ : ℝ) * cost w₁ p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [cost_cons, ih, NNReal.coe_add, NNReal.coe_mul]; ring

@[simp] theorem cost_unit {s t : V} (p : DWalk s t) :
    cost (fun _ _ => 1) p = (p.length : ℝ) := unit_cost p

theorem cost_bypass_le (w : V → V → ℝ≥0) {s t : V} (p : DWalk s t) :
    cost w p.bypass ≤ cost w p := by
  have h := Prod.Lex.monotone_fst_ofLex (score_bypass_le w p)
  simpa only [score_primary, cost] using h

/-- Positive summands make a proper sublist strictly cheaper. -/
theorem sublist_sum_eq_length {α : Type*} (f : α → ℝ)
    {l r : List α} (h : l.Sublist r) (hpos : ∀ a ∈ r, 0 < f a) :
    (l.map f).sum ≤ (r.map f).sum ∧
      ((l.map f).sum = (r.map f).sum → l.length = r.length) := by
  revert hpos
  induction h with
  | slnil => exact fun _ => ⟨le_rfl, fun _ => rfl⟩
  | cons a h ih =>
    intro hpos
    have ha := hpos a (by simp)
    have hi := ih (fun b hb => hpos b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons]
    constructor
    · linarith [hi.1]
    · intro he
      linarith [hi.1]
  | cons_cons a h ih =>
    intro hpos
    have hi := ih (fun b hb => hpos b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨add_le_add le_rfl hi.1, ?_⟩
    intro he
    simpa only [List.length_cons] using congrArg Nat.succ (hi.2 (by linarith))

/-- Equality after cycle erasure forces the original walk to be a path when
all allowed edge weights are positive. This excludes zero-cost cycles. -/
theorem isPath_of_cost_bypass_eq {G : V → V → Prop} {w : V → V → ℝ≥0}
    (hpos : ∀ u v, G u v → 0 < w u v) {s t : V} (p : DWalk s t)
    (hp : Allowed G p) (he : cost w p.bypass = cost w p) : p.IsPath := by
  have h := sublist_sum_eq_length (fun d : (⊤ : SimpleGraph V).Dart =>
    (w d.fst d.snd : ℝ)) p.darts_bypass_sublist_darts
    (fun d hd => by exact_mod_cast hpos d.fst d.snd (hp d hd))
  have hl : p.bypass.length = p.length := by
    simpa only [Walk.length_darts] using h.2 he
  exact Walk.bypass_eq_self_iff_isPath.mp
    ((Walk.length_le_bypass_length_iff p).mp hl.ge)

def Shortest (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (p : DWalk s t) : Prop :=
  Allowed G p ∧ ∀ q : DWalk s t, Allowed G q → cost w p ≤ cost w q

def MinHopShortest (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (p : DWalk s t) : Prop :=
  Shortest G w p ∧ ∀ q : DWalk s t, Shortest G w q → p.length ≤ q.length

def UniqueShortest (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (p : DWalk s t) : Prop :=
  Shortest G w p ∧ ∀ q : DWalk s t, Shortest G w q → q = p

theorem optimal_shortest {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : Optimal G w p) : Shortest G w p :=
  ⟨hp.1, hp.shortest⟩

theorem exists_shortest (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (h : Reachable G s t) :
    ∃ p : DWalk s t, p.IsPath ∧ Shortest G w p := by
  obtain ⟨p, hp⟩ := exists_optimal G w s t h
  exact ⟨p, hp.2.1, optimal_shortest hp⟩

theorem Shortest.cost_eq {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p q : DWalk s t} (hp : Shortest G w p) (hq : Shortest G w q) :
    cost w p = cost w q := le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)

theorem Shortest.isPath {G : V → V → Prop} {w : V → V → ℝ≥0}
    (hpos : ∀ u v, G u v → 0 < w u v)
    {s t : V} {p : DWalk s t} (hp : Shortest G w p) : p.IsPath := by
  apply isPath_of_cost_bypass_eq hpos p hp.1
  exact le_antisymm (cost_bypass_le w p) (hp.2 p.bypass (allowed_bypass hp.1))

/-- A contiguous subwalk of any shortest weighted walk is itself shortest. -/
theorem Shortest.subwalk {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t u v : V} {p : DWalk s t} (hp : Shortest G w p)
    {q : DWalk u v} (hsub : q.IsSubwalk p) : Shortest G w q := by
  obtain ⟨l, r, heq⟩ := hsub
  subst p
  have hall := (allowed_append G _ _).mp hp.1
  have hleft := (allowed_append G _ _).mp hall.1
  refine ⟨hleft.2, ?_⟩
  intro z hz
  have hvalid := (allowed_append G (l.append z) r).mpr
    ⟨(allowed_append G l z).mpr ⟨hleft.1, hz⟩, hall.2⟩
  have hm := hp.2 ((l.append z).append r) hvalid
  simpa only [cost_append, add_le_add_iff_right, add_le_add_iff_left] using hm

/-- Even with zero input weights, uniqueness prevents a shortest walk from
containing a removable cycle. -/
theorem UniqueShortest.isPath {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : UniqueShortest G w p) : p.IsPath := by
  have hb : Shortest G w p.bypass := ⟨allowed_bypass hp.1.1,
    fun q hq => (cost_bypass_le w p).trans (hp.1.2 q hq)⟩
  exact Walk.bypass_eq_self_iff_isPath.mp (hp.2 p.bypass hb)

theorem MinHopShortest.isPath {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : MinHopShortest G w p) : p.IsPath := by
  have hb : Shortest G w p.bypass := ⟨allowed_bypass hp.1.1,
    fun q hq => (cost_bypass_le w p).trans (hp.1.2 q hq)⟩
  exact Walk.bypass_eq_self_iff_isPath.mp
    ((Walk.length_le_bypass_length_iff p).mp (hp.2 p.bypass hb))

/-- A uniquely cheapest allowed simple path is uniquely cheapest among all
walks when every allowed edge has positive weight. -/
theorem uniqueShortest_of_path_comparison {G : V → V → Prop}
    {w : V → V → ℝ≥0} (hpos : ∀ u v, G u v → 0 < w u v)
    {s t : V} {p : DWalk s t} (hp : Allowed G p)
    (hmin : ∀ q : DWalk s t, Allowed G q → q.IsPath → q ≠ p → cost w p < cost w q) :
    UniqueShortest G w p := by
  have hshort : Shortest G w p := by
    refine ⟨hp, ?_⟩
    intro q hq
    by_cases he : q.bypass = p
    · rw [← he]
      exact cost_bypass_le w q
    · exact (hmin q.bypass (allowed_bypass hq) q.bypass_isPath he).le.trans
        (cost_bypass_le w q)
  refine ⟨hshort, ?_⟩
  intro q hq
  by_contra he
  exact (hmin q hq.1 (hq.isPath hpos) he).not_ge (hq.2 p hp)

end GreedyShortcuts.WeightedPaths
