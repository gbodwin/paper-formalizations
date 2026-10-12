import GreedyShortcuts.ComputedChainPacking

/-! The bounded executable packing is maximal, hence every original path has
fewer than r unused vertices. This is the full uncovered-subsequence guarantee. -/
namespace GreedyShortcuts.ComputedChainPacking
open Finset SimpleGraph DirectedPaths ChainUnion ComputedChainSearch CanonicalSegments
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ}

theorem exhausted (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (r : ℕ) (hr : 0<r) (k : ℕ) (S : Finset (Fin n)) (hk : S.card≤k) :
    find edge (fun v => decide (v∈(pack edge r k S).2)) r=none := by
  induction k generalizing S with
  | zero =>
    have hz : S=∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    simp only [pack]
    cases hf : find edge (fun v => decide (v∈(∅ : Finset (Fin n)))) r with
    | none => exact hf
    | some xs =>
      obtain ⟨hlen,_,hen⟩ := find_spec G hG edge he _ r hf
      have hx : xs=[] := List.eq_nil_iff_forall_not_mem.mpr (by simpa using hen)
      simp only [hx,List.length_nil] at hlen
      omega
  | succ k ih =>
    cases hf : find edge (fun v => decide (v∈S)) r with
    | none => simp only [pack,hf]
    | some xs =>
      simp only [pack,hf]
      obtain ⟨hlen,hchain,hen⟩ := find_spec G hG edge he _ r hf
      have hxs : xs.toFinset ⊆ S := by
        intro v hv
        exact of_decide_eq_true (hen v (List.mem_toFinset.mp hv))
      have hc : xs.toFinset.card=r := by rw [List.toFinset_card_of_nodup hchain.1,hlen]
      have hcard := Finset.card_sdiff_add_card_eq_card hxs
      exact ih (S \ xs.toFinset) (by omega)

/-- The actual final unused set contains no complete r-chain. -/
theorem no_remaining_chain (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (r : ℕ) (hr : 0<r) (c : UniformChainPacking.FixedChain G r) :
    ¬ c.chain.support ⊆ (pack edge r n Finset.univ).2 := by
  intro hc
  have hnone := exhausted G hG edge he r hr n Finset.univ (by simp)
  apply find_complete G hG edge he _ hr c ?_ hnone
  intro i
  exact decide_eq_true (hc (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem remaining_path_lt (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (r : ℕ) (hr : 0<r) {s t : Fin n} (p : DWalk s t) (hp : Allowed G p) :
    (p.support.toFinset ∩ (pack edge r n Finset.univ).2).card<r := by
  by_contra h
  obtain ⟨c,hc⟩ := UniformChainPacking.extract_chain p hp
    (ChainDistance.Context.allowed_isPath hG p hp) (pack edge r n Finset.univ).2 r (by omega)
  exact no_remaining_chain G hG edge he r hr c hc

end GreedyShortcuts.ComputedChainPacking
