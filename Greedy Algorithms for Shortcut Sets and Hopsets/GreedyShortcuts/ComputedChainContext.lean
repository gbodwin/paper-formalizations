import GreedyShortcuts.ComputedPackingCover
import GreedyShortcuts.ComputedPathFour

/-! Chain data and preprocessing obtained from the actual bounded packing.
Every data field is computed from the adjacency table and the chain length. -/
namespace GreedyShortcuts.ComputedChainPacking
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainUnion ComputedChainSearch
open ChainFirst ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ}

def chainOfList (G : Fin n → Fin n → Prop) (xs : List (Fin n)) (h : ChainList G xs) : Chain G where
  length := xs.length
  node := xs.get
  injective := h.1.injective_get
  forward := fun i j hij => h.2 i.val j.val i.isLt j.isLt hij

theorem chainOfList_support (G : Fin n → Fin n → Prop) (xs : List (Fin n)) (h : ChainList G xs) :
    (chainOfList G xs h).support=xs.toFinset := by
  ext v
  simp only [Chain.support,Finset.mem_image,Finset.mem_univ,true_and,List.mem_toFinset]
  exact List.mem_iff_get.symm

def lists (edge : Fin n → Fin n → Bool) (r : ℕ) : List (List (Fin n)) :=
  (pack edge r n Finset.univ).1

def chains (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (r : ℕ) :
    Fin (lists edge r).length → Chain G :=
  let cs := lists edge r
  fun i => chainOfList G cs[i] ((pack_spec G hG edge he r n Finset.univ).1 _ (List.getElem_mem _)).2

theorem chains_length (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (r : ℕ)
    (i : Fin (lists edge r).length) : (chains G hG edge he r i).length=r :=
  ((pack_spec G hG edge he r n Finset.univ).1 _ (List.getElem_mem _)).1

theorem chains_support (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (r : ℕ)
    (i : Fin (lists edge r).length) :
    (chains G hG edge he r i).support=((lists edge r)[i]).toFinset :=
  chainOfList_support G _ ((pack_spec G hG edge he r n Finset.univ).1 _ (List.getElem_mem _)).2

theorem chains_disjoint (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (r : ℕ) :
    Pairwise (fun i j => Disjoint (chains G hG edge he r i).support (chains G hG edge he r j).support) := by
  intro i j hij
  simp only [chains_support]
  have hpair := (pack_spec G hG edge he r n Finset.univ).2.1
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact List.pairwise_iff_get.mp hpair i j hlt
  · exact (List.pairwise_iff_get.mp hpair j i hgt).symm

def context (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (r : ℕ) :
    ChainDistance.Context (Fin n) (Fin (lists edge r).length) :=
  let W := PathFour.computedWitness r
  { G := G
    acyclic := hG
    chains := chains G hG edge he r
    disjoint := chains_disjoint G hG edge he r
    K := 6*PathFour.computedHeight r+1
    witnesses := fun i => (chains_length G hG edge he r i).symm ▸ W }

theorem chain_count (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (r : ℕ) :
    (lists edge r).length*r≤n := by
  have := pack_card G hG edge he r n Finset.univ
  simp only [Finset.card_univ,Fintype.card_fin] at this
  change (pack edge r n Finset.univ).1.length*r≤n
  omega

theorem context_cover (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (r : ℕ) (hr : 0<r) : IsCover (context G hG edge he r) (r-1) := by
  intro s t p hp _
  have hsub : uncovered (context G hG edge he r) p ⊆
      p.support.toFinset ∩ (pack edge r n Finset.univ).2 := by
    intro v hv
    obtain ⟨hvp,hlabel⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_inter.mpr ⟨hvp,?_⟩
    rw [(pack_spec G hG edge he r n Finset.univ).2.2.2]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hmem
    obtain ⟨xs,hxs,hvxs⟩ := mem_vertices.mp hmem
    change xs∈lists edge r at hxs
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hxs
    have hvchain : v∈(chains G hG edge he r i).support := by
      simp only [chains_support]
      change v∈((lists edge r).get i).toFinset
      rw [hi]
      exact List.mem_toFinset.mpr hvxs
    have hc := label_of_mem (chains G hG edge he r) (chains_disjoint G hG edge he r) hvchain
    change label (chains G hG edge he r) v=none at hlabel
    rw [hc] at hlabel
    cases hlabel
  have hh := (Finset.card_le_card hsub).trans_lt (remaining_path_lt G hG edge he r hr p hp)
  omega

end GreedyShortcuts.ComputedChainPacking
