import LengthExpander.Hikers

/-! Construct the actual stage permutation from the graph's matching labels.
The hiker protocol is therefore not supplied a matching oracle. -/
namespace LengthExpander
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

noncomputable def stageMate (G : SimpleGraph V) (index : Sym2 V → ℕ) (i : ℕ) (v : V) : V := by
  classical
  exact if h : ∃ u, G.Adj u v ∧ index s(u,v) = i then Classical.choose h else v

theorem stageMate_of_edge {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    {i : ℕ} {u v : V} (h : G.Adj u v) (hi : index s(u,v) = i) :
    stageMate G index i v = u := by
  classical
  have hex : ∃ u, G.Adj u v ∧ index s(u,v) = i := ⟨u,h,hi⟩
  simp only [stageMate, dif_pos hex]
  obtain ⟨hc,hci⟩ := Classical.choose_spec hex
  exact H _ u v hc h (hci.trans hi.symm)

theorem stageMate_cases (G : SimpleGraph V) (index : Sym2 V → ℕ) (i : ℕ) (v : V) :
    stageMate G index i v = v ∨
      (G.Adj (stageMate G index i v) v ∧ index s(stageMate G index i v,v) = i) := by
  classical
  by_cases hex : ∃ u, G.Adj u v ∧ index s(u,v) = i
  · right
    simpa only [stageMate, dif_pos hex] using Classical.choose_spec hex
  · left
    simp [stageMate, hex]

theorem stageMate_involutive {index : Sym2 V → ℕ} (H : MatchingLabels G index) (i : ℕ) :
    Function.Involutive (stageMate G index i) := by
  intro v
  rcases stageMate_cases G index i v with heq | ⟨hadj,hi⟩
  · rw [heq]; exact heq
  · apply stageMate_of_edge H hadj.symm
    simpa only [Sym2.eq_swap] using hi

noncomputable def matchingPermutation (G : SimpleGraph V) (index : Sym2 V → ℕ)
    (H : MatchingLabels G index) (i : ℕ) : Equiv.Perm V :=
  { toFun := stageMate G index i
    invFun := stageMate G index i
    left_inv := stageMate_involutive H i
    right_inv := stageMate_involutive H i }

theorem matchingPermutation_edge {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (i : ℕ) (v : V) (hm : matchingPermutation G index H i v ≠ v) :
    G.Adj v (matchingPermutation G index H i v) := by
  rcases stageMate_cases G index i v with heq | ⟨hadj,_⟩
  · exact False.elim (hm heq)
  · exact hadj.symm

theorem matchingPermutation_index {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (i : ℕ) (v : V) (hm : matchingPermutation G index H i v ≠ v) :
    index s(v,matchingPermutation G index H i v) = i := by
  rcases stageMate_cases G index i v with heq | ⟨_,hi⟩
  · exact False.elim (hm heq)
  · change index s(v,stageMate G index i v) = i
    simpa only [Sym2.eq_swap] using hi

/-- The concrete walk produced by processing the first k graph matchings. -/
noncomputable def graphHikerWalk {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (k : ℕ) (v : V) : G.Walk v (hikerPosition (matchingPermutation G index H) k v) :=
  hikerWalk (matchingPermutation G index H) (matchingPermutation_edge H) k v

theorem graphHikerWalk_increasing {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (k : ℕ) (v : V) : Increasing index (graphHikerWalk H k v) :=
  (hikerWalk_increasing (matchingPermutation G index H) (matchingPermutation_edge H)
    index (matchingPermutation_index H) k v).1

end LengthExpander
