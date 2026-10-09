import DegreeFaultSpanners.FaultSpanner
import DegreeFaultSpanners.Parameters
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.BigOperators

/-!
# Dense degree-fault witnesses at every finite order

A graph of maximum degree at most `f` has no proper `f`-degree-fault
spanner, at any stretch: the proposed spanner itself is an admissible
fault graph. Disjoint cliques of order `f + 1`, padded with isolated
vertices, therefore give actual witnesses with `N * f ≤ 4 * |E|`.
The boundary case `f = N` is supplied by the complete graph.
-/

namespace DegreeFaultSpanners

open SimpleGraph

/-- Every edge of a graph of maximum degree `f` is forced at every stretch. -/
theorem low_degree_spanner_eq {V : Type*} [Fintype V]
    {G H : SimpleGraph V} {f t : ℕ}
    (hdeg : HasDegreeBound G f) (h : IsDegreeFaultSpanner G H f t) : H = G := by
  apply le_antisymm h.1
  intro u v huv
  by_contra hmissing
  obtain ⟨p, _⟩ := h.edge_replacement ⟨h.1, hdeg.of_le h.1⟩ huv hmissing
  have pbot : (⊥ : SimpleGraph V).Walk u v := by simpa only [sdiff_self] using p
  exact huv.ne pbot.nil_of_bot.eq

/-- `q` disjoint cliques of order `s`, together with `r` isolated vertices. -/
def denseBlocks (q s r : ℕ) : SimpleGraph ((Fin q × Fin s) ⊕ Fin r) where
  Adj
    | .inl a, .inl b => a.1 = b.1 ∧ a.2 ≠ b.2
    | _, _ => False
  symm.symm := by
    rintro (a | a) (b | b) h <;> simp_all [eq_comm]
  loopless.irrefl := by
    rintro (a | a) <;> simp

@[simp] theorem denseBlocks_neighbor_ncard_inl (q s r : ℕ) (a : Fin q × Fin s) :
    ((denseBlocks q s r).neighborSet (.inl a)).ncard = s - 1 := by
  have hset : (denseBlocks q s r).neighborSet (.inl a) =
      (fun j : Fin s => (Sum.inl (a.1, j) : (Fin q × Fin s) ⊕ Fin r)) ''
        ((Set.univ : Set (Fin s)) \ {a.2}) := by
    ext x
    rcases x with ⟨i, j⟩ | x
    · simp only [SimpleGraph.mem_neighborSet, denseBlocks, Set.mem_image,
        Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and,
        Sum.inl.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hi, hj⟩
        exact ⟨j, Ne.symm hj, hi, rfl⟩
      · rintro ⟨z, hz, hi, rfl⟩
        exact ⟨hi, Ne.symm hz⟩
    · simp [SimpleGraph.mem_neighborSet, denseBlocks]
  rw [hset, Set.ncard_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.snd (Sum.inl.inj h)

@[simp] theorem denseBlocks_neighbor_ncard_inr (q s r : ℕ) (a : Fin r) :
    ((denseBlocks q s r).neighborSet (.inr a)).ncard = 0 := by
  have hset : (denseBlocks q s r).neighborSet (.inr a) = ∅ := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborSet, denseBlocks]
  rw [hset, Set.ncard_empty]

/-- Every non-isolated vertex has degree exactly `f`. -/
theorem denseBlocks_degree_bound (q f r : ℕ) :
    HasDegreeBound (denseBlocks q (f + 1) r) f := by
  rintro (a | a) <;> simp

/-- Exact degree-sum count for the actual clique-block graph. -/
theorem denseBlocks_twice_edges (q f r : ℕ) :
    2 * Nat.card (denseBlocks q (f + 1) r).edgeSet = q * (f + 1) * f := by
  classical
  calc
    2 * Nat.card (denseBlocks q (f + 1) r).edgeSet =
        ∑ v, ((denseBlocks q (f + 1) r).neighborSet v).ncard := by
      simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
        SimpleGraph.ncard_neighborSet] using
        (denseBlocks q (f + 1) r).sum_degrees_eq_twice_card_edges.symm
    _ = q * (f + 1) * f := by
      simp only [Fintype.sum_sum_type, denseBlocks_neighbor_ncard_inl,
        denseBlocks_neighbor_ncard_inr, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Nat.add_sub_cancel, smul_eq_mul,
        Nat.mul_zero, Nat.add_zero]

/-- Every `N ≥ 2` and `1 ≤ f ≤ N` admits an actual `N`-vertex graph with
at least `N*f/4` edges, all of which are forced in every degree-fault spanner.
The finite vertex type is explicit in the construction, and its size is exact. -/
theorem exists_dense_all_N (N f : ℕ) (hN : 2 ≤ N) (hf : 1 ≤ f) (hfN : f ≤ N) :
    ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
      letI : Fintype V := inst
      Fintype.card V = N ∧ HasDegreeBound G f ∧
      N * f ≤ 4 * Nat.card G.edgeSet ∧
      ∀ (t : ℕ) (H : SimpleGraph V), IsDegreeFaultSpanner G H f t → H = G := by
  classical
  let q := N / (f + 1)
  let r := N % (f + 1)
  have hdiv : q * (f + 1) + r = N := by
    simpa only [q, r, Nat.mul_comm] using Nat.div_add_mod N (f + 1)
  have hr : r < f + 1 := Nat.mod_lt N (by omega)
  by_cases hq : q = 0
  · have hdiv0 : r = N := by simpa only [hq, Nat.zero_mul, Nat.zero_add] using hdiv
    have hf_eq : f = N := by omega
    subst f
    have hdeg : HasDegreeBound (⊤ : SimpleGraph (Fin N)) N := by
      intro v
      rw [SimpleGraph.ncard_neighborSet, SimpleGraph.complete_graph_degree,
        Fintype.card_fin]
      omega
    refine ⟨Fin N, inferInstance, ⊤, by simp, hdeg, ?_, ?_⟩
    · have hcard : Nat.card (⊤ : SimpleGraph (Fin N)).edgeSet = N.choose 2 := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
          SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
      rw [hcard]
      simpa only [pow_two] using complete_graph_quadratic_lower_bound N hN
    · intro t H hH
      exact low_degree_spanner_eq hdeg hH
  · have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    have hblock : f + 1 ≤ q * (f + 1) := by
      simpa using Nat.mul_le_mul_right (f + 1) hqpos
    have hhalf : N ≤ 2 * (q * (f + 1)) := by omega
    have hcount := denseBlocks_twice_edges q f r
    refine ⟨(Fin q × Fin (f + 1)) ⊕ Fin r, inferInstance,
      denseBlocks q (f + 1) r, ?_, denseBlocks_degree_bound q f r, ?_, ?_⟩
    · simpa using hdiv
    · calc
        N * f ≤ (2 * (q * (f + 1))) * f := Nat.mul_le_mul_right f hhalf
        _ = 4 * Nat.card (denseBlocks q (f + 1) r).edgeSet := by nlinarith only [hcount]
    · intro t H hH
      exact low_degree_spanner_eq (denseBlocks_degree_bound q f r) hH

end DegreeFaultSpanners
