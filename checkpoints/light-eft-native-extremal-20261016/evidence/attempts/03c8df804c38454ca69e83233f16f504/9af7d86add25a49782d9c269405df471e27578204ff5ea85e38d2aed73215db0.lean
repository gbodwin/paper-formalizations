import LightSpanners.Distance
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace LightSpanners
open SimpleGraph
variable {V : Type*} [DecidableEq V]

structure UnitSpanningCycle (G : SimpleGraph V) (w : Sym2 V → ℝ) where
  base : V
  cycle : G.Walk base base
  hamiltonian : cycle.IsHamiltonianCycle
  unit : ∀ e ∈ cycle.edges, w e = 1
  lower : ∀ e ∈ G.edgeSet, 1 ≤ w e

omit [DecidableEq V] in
theorem walkWeight_eq_length_of_unit (w : Sym2 V → ℝ) {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (h : ∀ e ∈ p.edges, w e = 1) :
    walkWeight w p = p.length := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    simp only [walkWeight_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rw [h _ (by simp), ih (fun e he => h e (by simp [he]))]
    ring

namespace UnitSpanningCycle
variable {G : SimpleGraph V} {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w)
include C

theorem exists_short_arc (u v : V) :
    ∃ p : G.Walk u v, (∀ e ∈ p.edges, e ∈ C.cycle.edges) ∧
      2 * p.length ≤ C.cycle.length := by
  let c := C.cycle.rotate u (C.hamiltonian.mem_support u)
  have hv : v ∈ c.support :=
    (C.cycle.mem_support_rotate_iff u _).mpr (C.hamiltonian.mem_support v)
  let p := c.takeUntil v hv
  let q := c.dropUntil v hv
  have hsum : p.length + q.length = C.cycle.length := by
    rw [← Walk.length_append, Walk.take_spec, Walk.length_rotate]
  have hedge : ∀ e ∈ c.edges, e ∈ C.cycle.edges := fun e he =>
    (C.cycle.rotate_edges u _).perm.mem_iff.mp he
  by_cases hshort : 2 * p.length ≤ C.cycle.length
  · exact ⟨p, fun e he => hedge e (c.edges_takeUntil_subset_edges hv he), hshort⟩
  · refine ⟨q.reverse, ?_, ?_⟩
    · intro e he
      exact hedge e (c.edges_dropUntil_subset_edges hv (by simpa using he))
    · simp only [Walk.length_reverse]
      omega

variable [Fintype V]

theorem cycle_weight : walkWeight w C.cycle = Fintype.card V := by
  rw [walkWeight_eq_length_of_unit w C.cycle C.unit, C.hamiltonian.length_eq]

theorem three_le_card : 3 ≤ Fintype.card V := by
  rw [← C.hamiltonian.length_eq]
  exact C.hamiltonian.isCycle.three_le_length

theorem exists_short_path (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ (∀ e ∈ p.edges, e ∈ C.cycle.edges) ∧
      walkWeight w p ≤ (Fintype.card V : ℝ) / 2 := by
  obtain ⟨p, hp, hlen⟩ := C.exists_short_arc u v
  refine ⟨p.bypass, p.bypass_isPath, ?_, ?_⟩
  · exact fun e he => hp e (p.edges_bypass_sublist_edges.subset he)
  · have hunit : ∀ e ∈ p.bypass.edges, w e = 1 :=
      fun e he => C.unit e (hp e (p.edges_bypass_sublist_edges.subset he))
    rw [walkWeight_eq_length_of_unit w p.bypass hunit]
    have hb : p.bypass.length ≤ p.length := by
      simpa using p.edges_bypass_sublist_edges.length_le
    rw [C.hamiltonian.length_eq] at hlen
    have hr : (2 : ℝ) * p.bypass.length ≤ Fintype.card V := by
      exact_mod_cast (by omega : 2 * p.bypass.length ≤ Fintype.card V)
    linarith

theorem threshold_lt_card {g : ℝ} (hg : WeightedGirthAbove G w g) :
    g < Fintype.card V := by
  have hne : C.cycle.edges ≠ [] := by
    intro he
    have : C.cycle.length = 0 := by simpa using congrArg List.length he
    have := C.hamiltonian.isCycle.three_le_length
    omega
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  have h := hg C.base C.cycle C.hamiltonian.isCycle e he
  simpa only [C.unit e he, mul_one, C.cycle_weight] using h

/-- The short-arc argument of Lemma 3.7 bounds non-cycle edges. -/
theorem chord_weight_lt {g : ℝ} (hg : WeightedGirthAbove G w g) (hg1 : 1 < g)
    {u v : V} (h : G.Adj u v) (hchord : s(u,v) ∉ C.cycle.edges) :
    w s(u,v) < (Fintype.card V : ℝ) / (2 * (g - 1)) := by
  obtain ⟨p, hp, he, hweight⟩ := C.exists_short_path v u
  have hnot : s(u,v) ∉ p.edges := fun hx => hchord (he _ hx)
  have hc : (Walk.cons h p).IsCycle := (p.cons_isCycle_iff h).mpr ⟨hp, hnot⟩
  have hh := hg u (.cons h p) hc s(u,v) (by simp)
  simp only [walkWeight_cons] at hh
  apply (lt_div_iff₀ (by linarith : 0 < 2 * (g - 1))).mpr
  nlinarith

theorem edge_weight_le_max {g : ℝ} (hg : WeightedGirthAbove G w g) (hg1 : 1 < g)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    w e ≤ max 1 ((Fintype.card V : ℝ) / (2 * (g - 1))) := by
  by_cases hc : e ∈ C.cycle.edges
  · rw [C.unit e hc]
    exact le_max_left _ _
  · induction e using Sym2.inductionOn with
    | hf u v =>
      exact (C.chord_weight_lt hg hg1 ((mem_edgeSet G).mp he) hc).le.trans (le_max_right _ _)

end UnitSpanningCycle
end LightSpanners
