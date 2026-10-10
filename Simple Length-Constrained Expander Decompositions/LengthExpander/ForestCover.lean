import LengthExpander.SparseOrder
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.EquivFin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

def graphOn (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm.symm _ _ h := ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless.irrefl _ h := h.1.ne rfl

theorem graphOn_mono (G : SimpleGraph V) {S T : Finset V} (h : S ⊆ T) :
    graphOn G S ≤ graphOn G T := fun _ _ huv => ⟨huv.1,h huv.2.1,h huv.2.2⟩

noncomputable def assignedEdge {K : ℕ} (v : V) (N : Finset V)
    (c : N ↪ Fin K) (i : Fin K) : SimpleGraph V := by
  classical
  exact if h : ∃ w : N, c w = i then edge v ((Classical.choose h : N) : V) else ⊥

theorem assignedEdge_of {K : ℕ} (v : V) (N : Finset V)
    (c : N ↪ Fin K) (w : N) : assignedEdge v N c (c w) = edge v (w : V) := by
  classical
  have hex : ∃ z : N, c z = c w := ⟨w,rfl⟩
  rw [assignedEdge,dif_pos hex]
  exact congrArg (fun z : N => edge v (z : V)) (c.injective (Classical.choose_spec hex))

theorem assignedEdge_cases {K : ℕ} (v : V) (N : Finset V)
    (c : N ↪ Fin K) (i : Fin K) :
    assignedEdge v N c i = ⊥ ∨ ∃ w : N, assignedEdge v N c i = edge v (w : V) := by
  classical
  by_cases h : ∃ w : N, c w = i
  · exact Or.inr ⟨Classical.choose h,by simp [assignedEdge,h]⟩
  · exact Or.inl (by simp [assignedEdge,h])

/-- A sparse elimination order constructs a cover by K actual acyclic graphs.
At each insertion, its later neighbors are assigned distinct forests, so each
forest receives at most one edge incident to the formerly isolated vertex. -/
theorem forest_cover_of_sparse_order (G : SimpleGraph V) (K : ℕ)
    {L : List V} (horder : SparseOrder G K L) (hnd : L.Nodup) :
    ∃ F : Fin K → SimpleGraph V,
      (∀ i, (F i).IsAcyclic) ∧ (∀ i, F i ≤ graphOn G L.toFinset) ∧
      (∀ u v, (graphOn G L.toFinset).Adj u v → ∃ i, (F i).Adj u v) := by
  classical
  induction horder with
  | nil =>
    refine ⟨fun _ => ⊥,fun _ => isAcyclic_bot,fun _ => bot_le,?_⟩
    intro u v h
    have hf : False := by simpa using h.2.1
    exact hf.elim
  | @cons v L horder hdeg ih =>
    have hv : v ∉ L := (List.nodup_cons.mp hnd).1
    obtain ⟨F,hFacyc,hFsub,hFcover⟩ := ih (List.nodup_cons.mp hnd).2
    let N := L.toFinset.filter (G.Adj v)
    have hcard : Fintype.card N ≤ Fintype.card (Fin K) := by simpa [N] using hdeg
    obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hcard
    let F' : Fin K → SimpleGraph V := fun i => F i ⊔ assignedEdge v N c i
    have hN : ∀ w : N, (w : V) ∈ L.toFinset ∧ G.Adj v w := fun w => mem_filter.mp w.property
    have hvw : ∀ w : N, v ≠ (w : V) := by
      intro w he
      exact hv (List.mem_toFinset.mp (he ▸ (hN w).1))
    have hisolated : ∀ i, (F i).neighborSet v = ∅ := by
      intro i
      ext w
      constructor
      · intro hw
        exact (hv (List.mem_toFinset.mp (hFsub i hw).2.1)).elim
      · simp
    have hnew : ∀ i, assignedEdge v N c i ≤ graphOn G (v :: L).toFinset := by
      intro i
      rcases assignedEdge_cases v N c i with he | ⟨w,he⟩
      · rw [he]; exact bot_le
      · rw [he]
        apply (edge_le_iff (graphOn G (v :: L).toFinset)).mpr
        exact Or.inr ⟨(hN w).2,by simp,by simpa using Or.inr (hN w).1⟩
    have hstar : ∀ w : N, ∃ i, (F' i).Adj v w := by
      intro w
      refine ⟨c w,Or.inr ?_⟩
      rw [assignedEdge_of]
      exact (edge_adj v (w : V) v (w : V)).mpr ⟨Or.inl ⟨rfl,rfl⟩,hvw w⟩
    refine ⟨F',?_,?_,?_⟩
    · intro i
      rcases assignedEdge_cases v N c i with he | ⟨w,he⟩
      · simpa [F',he] using hFacyc i
      · simp only [F',he]
        exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable
          (not_reachable_of_neighborSet_left_eq_empty (hvw w) (hisolated i)) (hFacyc i)
    · intro i
      exact sup_le ((hFsub i).trans (graphOn_mono G (by simp))) (hnew i)
    · intro u z h
      obtain ⟨hadj,hu,hz⟩ := h
      have hu' : u = v ∨ u ∈ L.toFinset := by simpa using hu
      have hz' : z = v ∨ z ∈ L.toFinset := by simpa using hz
      rcases hu' with heu | huL
      · subst u
        have hzL : z ∈ L.toFinset := hz'.resolve_left hadj.ne.symm
        exact hstar ⟨z,mem_filter.mpr ⟨hzL,hadj⟩⟩
      · rcases hz' with hez | hzL
        · subst z
          obtain ⟨i,hi⟩ := hstar ⟨u,mem_filter.mpr ⟨huL,hadj.symm⟩⟩
          exact ⟨i,hi.symm⟩
        · obtain ⟨i,hi⟩ := hFcover u z ⟨hadj,huL,hzL⟩
          exact ⟨i,Or.inl hi⟩

variable [Fintype V] {G : SimpleGraph V}

/-- Theorem 1.3 as an explicit forest-cover existence theorem. The bound is
ceil(8s n^(2/s)); every returned member is an actual acyclic subgraph and their
union covers every edge. No Nash–Williams or arboricity oracle is assumed. -/
theorem parallelGreedy_forest_cover {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (hs : 2 ≤ s) :
    ∃ F : Fin (densityBudget (Fintype.card V) s) → SimpleGraph V,
      (∀ i, (F i).IsAcyclic) ∧ (∀ i, F i ≤ G) ∧
      (∀ u v, G.Adj u v → ∃ i, (F i).Adj u v) := by
  classical
  obtain ⟨L,hnd,hL,horder⟩ := parallelGreedy_sparse_order H hs
  obtain ⟨F,ha,hle,hcover⟩ := forest_cover_of_sparse_order G _ horder hnd
  have hG : graphOn G L.toFinset = G := by
    rw [hL]
    ext u v
    simp [graphOn]
  refine ⟨F,ha,?_,?_⟩
  · simpa only [hG] using hle
  · simpa only [hG] using hcover

end LengthExpander
