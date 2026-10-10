import LengthExpander.HereditaryDensity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

/-- An explicit elimination order: each vertex has at most K neighbors
later in the list. Distinctness is maintained separately. -/
inductive SparseOrder (G : SimpleGraph V) (K : ℕ) : List V → Prop
  | nil : SparseOrder G K []
  | cons (v : V) (L : List V) (tail : SparseOrder G K L)
      (degree : (L.toFinset.filter (G.Adj v)).card ≤ K) : SparseOrder G K (v :: L)

/-- Repeatedly removing a low-degree vertex constructs a genuine finite
ordering, rather than assuming a degeneracy or forest-cover conclusion. -/
theorem exists_sparse_order (G : SimpleGraph V) (K : ℕ)
    (hlow : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ K)
    (S : Finset V) :
    ∃ L : List V, L.Nodup ∧ L.toFinset = S ∧ SparseOrder G K L := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨v,hv,hdeg⟩ := hlow S hS
      obtain ⟨L,hL,heq,horder⟩ := ih (S.erase v) (erase_ssubset hv)
      refine ⟨v :: L, ?_, ?_, SparseOrder.cons v L horder ?_⟩
      · exact List.nodup_cons.mpr ⟨by simpa [← List.mem_toFinset,heq] using notMem_erase v S,hL⟩
      · simpa only [List.toFinset_cons,heq] using insert_erase hv
      · rw [heq]
        exact (card_le_card (filter_subset_filter _ (erase_subset v S))).trans hdeg
    · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨[],by simp,by simp,SparseOrder.nil⟩

variable [Fintype V]

noncomputable def densityBudget (n s : ℕ) : ℕ :=
  ⌈8 * (s : ℝ) * (n : ℝ)^(2/(s : ℝ))⌉₊

/-- The degree in an induced graph is the count of retained neighbors. -/
theorem degree_induce_eq_filter (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = (S.filter (G.Adj v)).card := by
  classical
  have heq := G.map_neighborFinset_induce (s := (S : Set V)) v
  have hc := congrArg Finset.card heq
  rw [card_map,SimpleGraph.card_neighborFinset_eq_degree] at hc
  calc
    _ = (G.neighborFinset (v : V) ∩ (S : Set V).toFinset).card := by
      convert hc using 1 <;> (try dsimp only [SimpleGraph.degree]) <;>
        apply congrArg Finset.card <;> ext u <;>
          simp only [mem_neighborFinset,mem_inter,Set.mem_toFinset]
    _ = _ := by
      congr 1
      ext u
      simp [mem_neighborFinset,and_comm]

/-- The original graph now has an explicit finite sparse ordering with the
uniform O(s n^(2/s)) budget. A forest partition is the next separate step. -/
theorem parallelGreedy_sparse_order {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (hs : 2 ≤ s) :
    ∃ L : List V, L.Nodup ∧ L.toFinset = univ ∧
      SparseOrder G (densityBudget (Fintype.card V) s) L := by
  apply exists_sparse_order
  intro S hS
  obtain ⟨v,hv⟩ := hereditary_low_degree H hs S hS
  refine ⟨v,v.property,?_⟩
  rw [← degree_induce_eq_filter S v]
  have hceil := Nat.le_ceil (8 * (s : ℝ) * (Fintype.card V : ℝ)^(2/(s : ℝ)))
  unfold densityBudget
  exact_mod_cast hv.trans hceil

end LengthExpander
