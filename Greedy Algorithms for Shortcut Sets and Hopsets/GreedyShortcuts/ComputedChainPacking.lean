import GreedyShortcuts.ComputedChainSearch

/-! A finite, literal remove-and-search chain packing. Each successful search
removes exactly r previously unused vertices. No maximum packing is chosen. -/
namespace GreedyShortcuts.ComputedChainPacking
open Finset DirectedPaths ChainUnion ComputedChainSearch CanonicalSegments
variable {n : ℕ}

def vertices : List (List (Fin n)) → Finset (Fin n)
  | [] => ∅
  | xs::cs => xs.toFinset ∪ vertices cs

@[simp] theorem mem_vertices {cs : List (List (Fin n))} {v : Fin n} :
    v∈vertices cs ↔ ∃xs∈cs,v∈xs := by
  induction cs with
  | nil => simp [vertices]
  | cons xs cs ih => simp [vertices,ih,or_and_right,exists_or]

def pack (edge : Fin n → Fin n → Bool) (r : ℕ) :
    ℕ → Finset (Fin n) → List (List (Fin n)) × Finset (Fin n)
  | 0,S => ([],S)
  | k+1,S => match find edge (fun v => decide (v∈S)) r with
    | none => ([],S)
    | some xs => let rest := pack edge r k (S \ xs.toFinset)
                 (xs::rest.1,rest.2)

/-- The returned lists are genuine disjoint r-chains in the initial domain;
the second component is exactly its complement. -/
theorem pack_spec (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (r k : ℕ) (S : Finset (Fin n)) :
    (∀xs∈(pack edge r k S).1,xs.length=r ∧ ChainList G xs) ∧
    (pack edge r k S).1.Pairwise (fun xs ys => Disjoint xs.toFinset ys.toFinset) ∧
    vertices (pack edge r k S).1 ⊆ S ∧
    (pack edge r k S).2=S \ vertices (pack edge r k S).1 := by
  induction k generalizing S with
  | zero => simp [pack,vertices]
  | succ k ih =>
    simp only [pack]
    split <;> rename_i hf
    · simp [vertices]
    · rename_i xs
      obtain ⟨hlen,hchain,hen⟩ := find_spec G hG edge he _ r hf
      have hxs : xs.toFinset ⊆ S := by
        intro v hv
        exact of_decide_eq_true (hen v (List.mem_toFinset.mp hv))
      obtain ⟨hvalid,hdisj,hsub,hrem⟩ := ih (S \ xs.toFinset)
      dsimp only
      refine ⟨?_,?_,?_,?_⟩
      · intro ys hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨hlen,hchain⟩
        · exact hvalid ys hy
      · apply List.pairwise_cons.mpr
        refine ⟨?_,hdisj⟩
        intro ys hy
        apply Finset.disjoint_left.mpr
        intro v hvx hvy
        have hv := hsub (mem_vertices.mpr ⟨ys,hy,List.mem_toFinset.mp hvy⟩)
        exact (Finset.mem_sdiff.mp hv).2 hvx
      · exact Finset.union_subset hxs (hsub.trans Finset.sdiff_subset)
      · rw [hrem]
        ext v
        simp [vertices]
        tauto

/-- Exact accounting for every removed vertex. -/
theorem pack_card (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (r k : ℕ) (S : Finset (Fin n)) :
    (pack edge r k S).2.card+(pack edge r k S).1.length*r=S.card := by
  induction k generalizing S with
  | zero => simp [pack]
  | succ k ih =>
    simp only [pack]
    split <;> rename_i hf
    · simp
    · rename_i xs
      obtain ⟨hlen,hchain,hen⟩ := find_spec G hG edge he _ r hf
      have hxs : xs.toFinset ⊆ S := by
        intro v hv
        exact of_decide_eq_true (hen v (List.mem_toFinset.mp hv))
      have hc : xs.toFinset.card=r := by rw [List.toFinset_card_of_nodup hchain.1,hlen]
      have heq := Finset.card_sdiff_add_card_eq_card hxs
      have hi := ih (S \ xs.toFinset)
      dsimp only
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

end GreedyShortcuts.ComputedChainPacking
