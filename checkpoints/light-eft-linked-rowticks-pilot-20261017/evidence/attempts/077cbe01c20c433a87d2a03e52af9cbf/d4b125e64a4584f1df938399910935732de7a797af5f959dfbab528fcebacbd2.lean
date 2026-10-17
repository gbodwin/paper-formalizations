import LightSpanners.Basic
import Mathlib.Data.Finset.Max

/-! Normalized weighted girth, scaling, and rounding in Section 3.2. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*}

theorem walkWeight_mono {w w' : Sym2 V → ℝ} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (h : ∀ e ∈ p.edges, w e ≤ w' e) :
    walkWeight w p ≤ walkWeight w' p := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    simp only [walkWeight_cons]
    exact add_le_add (h _ (by simp)) (ih (fun e he => h e (by simp [he])))

theorem walkWeight_scale (w : Sym2 V → ℝ) (c : ℝ) {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) :
    walkWeight (fun e => c * w e) p = c * walkWeight w p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [walkWeight_cons, ih]; ring

theorem walkWeight_le_length_mul {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (w : Sym2 V → ℝ) (M : ℝ) (h : ∀ e ∈ p.edges, w e ≤ M) :
    walkWeight w p ≤ p.length * M := by
  induction p with
  | nil => simp
  | @cons u v z hadj p ih =>
    have htail := ih (fun e he => h e (by simp [he]))
    have hhead := h s(u,v) (by simp)
    simp only [walkWeight_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem walkWeight_eq_length_mul {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (w : Sym2 V → ℝ) (M : ℝ) (h : ∀ e ∈ p.edges, w e = M) :
    walkWeight w p = p.length * M := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    simp only [walkWeight_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rw [h _ (by simp), ih (fun e he => h e (by simp [he]))]
    ring

theorem cycle_edges_nonempty {G : SimpleGraph V} {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) : p.edges ≠ [] := by
  intro h
  have : p.length = 0 := by simpa using congrArg List.length h
  have := hp.three_le_length
  omega

theorem exists_max_cycle_edge (w : Sym2 V → ℝ) {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ e ∈ p.edges, ∀ d ∈ p.edges, w d ≤ w e := by
  classical
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (cycle_edges_nonempty p hp)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image p.edges.toFinset w
    ⟨e, List.mem_toFinset.mpr he⟩
  exact ⟨m, List.mem_toFinset.mp hm, fun d hd => hmax d (List.mem_toFinset.mpr hd)⟩

noncomputable def cycleMaxWeight (w : Sym2 V → ℝ) {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) : ℝ :=
  w (Classical.choose (exists_max_cycle_edge w p hp))

theorem cycleMaxWeight_spec (w : Sym2 V → ℝ) {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) :
    (∃ e ∈ p.edges, cycleMaxWeight w p hp = w e) ∧
      ∀ e ∈ p.edges, w e ≤ cycleMaxWeight w p hp := by
  have h := Classical.choose_spec (exists_max_cycle_edge w p hp)
  exact ⟨⟨_, h.1, rfl⟩, h.2⟩

theorem cycleMaxWeight_pos {w : Sym2 V → ℝ} {G : SimpleGraph V}
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    0 < cycleMaxWeight w p hp := by
  obtain ⟨e, he, hmax⟩ := (cycleMaxWeight_spec w p hp).1
  rw [hmax]
  exact hw e (p.edges_subset_edgeSet he)

noncomputable def normalizedCycleWeight (w : Sym2 V → ℝ) {G : SimpleGraph V}
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) : ℝ :=
  walkWeight w p / cycleMaxWeight w p hp

theorem weightedGirthAbove_iff_normalized {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) {g : ℝ} (hg : 0 ≤ g) :
    WeightedGirthAbove G w g ↔ ∀ a (p : G.Walk a a) (hp : p.IsCycle),
      g < normalizedCycleWeight w p hp := by
  constructor
  · intro h a p hp
    apply (lt_div_iff₀ (cycleMaxWeight_pos hw p hp)).mpr
    obtain ⟨e, he, hmax⟩ := (cycleMaxWeight_spec w p hp).1
    rw [hmax]
    exact h a p hp e he
  · intro h a p hp e he
    have hm := (lt_div_iff₀ (cycleMaxWeight_pos hw p hp)).mp (h a p hp)
    exact (mul_le_mul_of_nonneg_left ((cycleMaxWeight_spec w p hp).2 e he) hg).trans_lt hm

theorem weightedGirthAbove_scale_iff {G : SimpleGraph V} {w : Sym2 V → ℝ}
    {g c : ℝ} (hc : 0 < c) :
    WeightedGirthAbove G (fun e => c * w e) g ↔ WeightedGirthAbove G w g := by
  constructor <;> intro h a p hp e he
  · have hh := h a p hp e he
    simp only [walkWeight_scale] at hh
    rw [mul_left_comm g c] at hh
    exact (mul_lt_mul_iff_of_pos_left hc).mp hh
  · simp only [walkWeight_scale]
    rw [mul_left_comm g c]
    exact mul_lt_mul_of_pos_left (h a p hp e he) hc

theorem isSpanner_scale_iff {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t c : ℝ} (hc : 0 < c) :
    IsSpanner G H (fun e => c * w e) t ↔ IsSpanner G H w t := by
  constructor <;> rintro ⟨hsub, h⟩ <;> refine ⟨hsub, fun u v p => ?_⟩
  · obtain ⟨q, hq⟩ := h u v p
    simp only [walkWeight_scale] at hq
    rw [mul_left_comm t c] at hq
    exact ⟨q, (mul_le_mul_iff_of_pos_left hc).mp hq⟩
  · obtain ⟨q, hq⟩ := h u v p
    refine ⟨q, ?_⟩
    simp only [walkWeight_scale]
    rw [mul_left_comm t c]
    exact mul_le_mul_of_nonneg_left hq hc.le

/-- Rounding also covers cycles whose original maximum weight is below one. -/
theorem WeightedGirthAbove.round_up {G : SimpleGraph V} {w : Sym2 V → ℝ}
    {g : ℝ} (hG : WeightedGirthAbove G w g) (hg : 0 ≤ g)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) :
    WeightedGirthAbove G (fun e => max 1 (w e)) g := by
  intro a p hp e he
  obtain ⟨m, hm, hmax⟩ := exists_max_cycle_edge w p hp
  have hbound := hG a p hp m hm
  have hpos := hw m (p.edges_subset_edgeSet hm)
  by_cases hlarge : 1 ≤ w m
  · have hemax : max 1 (w e) ≤ w m := max_le hlarge (hmax e he)
    exact (mul_le_mul_of_nonneg_left hemax hg).trans_lt
      (hbound.trans_le (walkWeight_mono p (fun _ _ => le_max_right _ _)))
  · have hround : ∀ d ∈ p.edges, max 1 (w d) = 1 := by
      intro d hd
      exact max_eq_left ((hmax d hd).trans (le_of_not_ge hlarge))
    have hsum := walkWeight_le_length_mul p w (w m) hmax
    have hlength : g < p.length := (mul_lt_mul_iff_of_pos_right hpos).mp
      (hbound.trans_le hsum)
    change g * max 1 (w e) < walkWeight (fun d => max 1 (w d)) p
    rw [hround e he, mul_one, walkWeight_eq_length_mul p _ 1 hround, mul_one]
    exact hlength

end LightSpanners
