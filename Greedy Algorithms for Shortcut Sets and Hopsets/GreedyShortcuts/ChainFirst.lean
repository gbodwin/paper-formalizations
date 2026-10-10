import GreedyShortcuts.ChainUnion

/-! Actual chain labels and earliest reachable entry vertices for a finite
vertex-disjoint chain family. No hereditary-optimality property is asserted. -/
namespace GreedyShortcuts.ChainFirst

open Finset DirectedPaths ChainUnion
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable {G : V → V → Prop}

theorem chain_unique (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    {v : V} {i j : I} (hi : v ∈ (C i).support) (hj : v ∈ (C j).support) : i = j := by
  by_contra hn
  exact Finset.disjoint_left.mp (hdisj hn) hi hj

noncomputable def label (C : I → Chain G) (v : V) : Option I := by
  classical
  exact if h : ∃ c,v ∈ (C c).support then some (Classical.choose h) else none

theorem label_of_mem (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    {c : I} {v : V} (hv : v ∈ (C c).support) : label C v = some c := by
  classical
  have hex : ∃ c,v ∈ (C c).support := ⟨c,hv⟩
  have he := chain_unique C hdisj (Classical.choose_spec hex) hv
  simp [label,hex,he]

theorem mem_of_label (C : I → Chain G) {c : I} {v : V} (hv : label C v = some c) :
    v ∈ (C c).support := by
  classical
  unfold label at hv
  split at hv
  next h =>
    have he : Classical.choose h = c := Option.some.inj hv
    simpa only [he] using Classical.choose_spec h
  next h => cases hv

noncomputable def reachableIndices (C : I → Chain G) (s : V) (c : I) : Finset (Fin (C c).length) := by
  classical
  exact Finset.univ.filter (fun i => Reachable G s ((C c).node i))

noncomputable def entry (C : I → Chain G) (s : V) (c : I) : V := by
  classical
  exact if h : (reachableIndices C s c).Nonempty then
    (C c).node ((reachableIndices C s c).min' h) else s

noncomputable def first (C : I → Chain G) (s v : V) : V :=
  match label C v with
  | none => s
  | some c => entry C s c

theorem first_constant (C : I → Chain G) (s u v : V) (h : label C u = label C v) :
    first C s u = first C s v := by simp only [first,h]

theorem label_node (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    (c : I) (i : Fin (C c).length) : label C ((C c).node i) = some c :=
  label_of_mem C hdisj (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

/-- The selector has exactly the properties needed for normalization:
reachable from the source, preceding the target along the same chain, and
constant over all vertices of that chain. -/
theorem first_spec (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    (s v : V) (hr : Reachable G s v) (hc : label C v ≠ none) :
    Reachable G s (first C s v) ∧ Reachable G (first C s v) v ∧ label C (first C s v) = label C v := by
  classical
  obtain ⟨c,hcv⟩ := Option.ne_none_iff_exists'.mp hc
  have hmem := mem_of_label C hcv
  obtain ⟨i,hi,hiv⟩ := Finset.mem_image.mp hmem
  have hir : i ∈ reachableIndices C s c :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hiv] using hr⟩
  have hne : (reachableIndices C s c).Nonempty := ⟨i,hir⟩
  let j := (reachableIndices C s c).min' hne
  have hj : j ∈ reachableIndices C s c := Finset.min'_mem _ _
  have hji : j ≤ i := Finset.min'_le _ _ hir
  have hentry : first C s v = (C c).node j := by simp [first,hcv,entry,hne,j]
  rw [hentry]
  refine ⟨(Finset.mem_filter.mp hj).2,?_,?_⟩
  · rw [← hiv]
    rcases lt_or_eq_of_le hji with hlt | rfl
    · exact (C c).forward _ _ hlt
    · exact reachable_refl G _
  · rw [label_node C hdisj,hcv]

end GreedyShortcuts.ChainFirst
