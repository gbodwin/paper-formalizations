import MinorFreeSpanners.SelectedStarHost

/-! Restrict a genuine selected star family to its literal covered vertex
set. No residual vertices or full-coverage hypothesis are silently supplied. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*}

abbrev SelectedStarVertex (C : Finset V) (L : V → Finset V) :=
  {x : V // x ∈ C ∪ C.biUnion L}

noncomputable def selectedStarCenters (C : Finset V) (L : V → Finset V) :
    Finset (SelectedStarVertex C L) := C.subtype (· ∈ C ∪ C.biUnion L)

noncomputable def selectedStarLeaves (C : Finset V) (L : V → Finset V) :
    Finset (SelectedStarVertex C L) := (C.biUnion L).subtype (· ∈ C ∪ C.biUnion L)

noncomputable def selectedStarAssignment (C : Finset V) (L : V → Finset V)
    (b : SelectedStarVertex C L) : Finset (SelectedStarVertex C L) :=
  (L b.val).subtype (· ∈ C ∪ C.biUnion L)

/-- Every assigned leaf has an actual owner among the selected centers. -/
theorem IsStarPacking.assigned_mem_selected {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    {b x : V} (hx : x ∈ L b) : x ∈ C.biUnion L := by
  have hb : b ∈ C := by
    by_contra hn
    simp only [h.1 b hn,Finset.notMem_empty] at hx
  exact Finset.mem_biUnion.mpr ⟨b,hb,hx⟩

/-- Passing to the actual covered-vertex subtype loses no assigned leaf. -/
theorem IsStarPacking.selected_assignment_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (b : SelectedStarVertex C L) :
    (selectedStarAssignment C L b).card=(L b.val).card := by
  rw [selectedStarAssignment,Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun _ hx =>
    Finset.mem_union_right C (h.assigned_mem_selected hx))

/-- The literal assignment remains a full compatible induced-star packing
on the actual induced graph, with all finite vertex types explicit. -/
theorem IsStarPacking.induce_selected {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L) :
    IsStarPacking (G.induce ((C ∪ C.biUnion L:Finset V):Set V))
      (selectedStarLeaves C L) (selectedStarCenters C L) ell
      (selectedStarAssignment C L) := by
  classical
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b hb
    have hb' : b.val ∉ C := by simpa only [selectedStarCenters,Finset.mem_subtype] using hb
    ext x
    simp [selectedStarAssignment,h.1 b.val hb']
  · intro b x hx
    simp only [selectedStarAssignment,Finset.mem_subtype] at hx
    exact Finset.mem_subtype.mpr (h.assigned_mem_selected hx)
  · intro b x hx
    exact h.2.2.1 b.val x.val (Finset.mem_subtype.mp hx)
  · intro b x hx y hy hxy he
    exact h.2.2.2.1 b.val x.val (Finset.mem_subtype.mp hx) y.val
      (Finset.mem_subtype.mp hy) (fun he => hxy (Subtype.ext he)) he
  · intro b c hbc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (h.2.2.2.2.1 b.val c.val
      (fun he => hbc (Subtype.ext he))) (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
  · intro b
    rw [h.selected_assignment_card]
    exact h.2.2.2.2.2 b.val

/-- The selected induced family really covers every vertex of its host. -/
theorem selected_star_family_covers (C : Finset V) (L : V → Finset V) :
    (selectedStarCenters C L).biUnion (fun b => insert b (selectedStarAssignment C L b)) =
      Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro x
  rcases Finset.mem_union.mp x.property with hx|hx
  · exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_subtype.mpr hx,Finset.mem_insert_self _ _⟩
  · obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
    let c : SelectedStarVertex C L := ⟨b,Finset.mem_union_left _ hb⟩
    exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_subtype.mpr hb,
      Finset.mem_insert_of_mem (Finset.mem_subtype.mpr hx)⟩

/-- Selected leaf and center domains are disjoint actual subtype sets. -/
theorem IsStarPacking.selected_domains_disjoint {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : Disjoint (selectedStarLeaves C L) (selectedStarCenters C L) := by
  apply Finset.disjoint_left.mpr
  intro x hx hc
  exact Finset.disjoint_left.mp hAC (h.covered_subset (Finset.mem_subtype.mp hx))
    (Finset.mem_subtype.mp hc)

/-- Full sizes are preserved under the actual subtype restriction. -/
theorem IsStarPacking.induce_selected_full {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hf : ∀ b ∈ C, (L b).card=ell) :
    ∀ b ∈ selectedStarCenters C L, (selectedStarAssignment C L b).card=ell := by
  intro b hb
  rw [h.selected_assignment_card,hf b.val (Finset.mem_subtype.mp hb)]

/-- Original bipartition becomes the exact covered-leaf/center bipartition
of the induced selected host. -/
theorem IsStarPacking.selected_host_bipartite {G : SimpleGraph V} {A B C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B) :
    (G.induce ((C ∪ C.biUnion L:Finset V):Set V)).IsBipartiteWith
      (selectedStarLeaves C L:Set (SelectedStarVertex C L))
      (selectedStarCenters C L:Set (SelectedStarVertex C L)) := by
  classical
  have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
  have ha : ∀ x : SelectedStarVertex C L, x.val ∈ A → x ∈ selectedStarLeaves C L := by
    intro x hx
    apply Finset.mem_subtype.mpr
    rcases Finset.mem_union.mp x.property with hc|hl
    · exact (Finset.disjoint_left.mp hAC hx hc).elim
    · exact hl
  have hb : ∀ x : SelectedStarVertex C L, x.val ∈ B → x ∈ selectedStarCenters C L := by
    intro x hx
    apply Finset.mem_subtype.mpr
    rcases Finset.mem_union.mp x.property with hc|hl
    · exact hc
    · exact (Set.disjoint_left.mp hG.disjoint (h.covered_subset hl) hx).elim
  refine ⟨Finset.disjoint_coe.mpr (h.selected_domains_disjoint hAC),?_⟩
  intro x y he
  rcases hG.mem_of_adj he with ⟨hx,hy⟩|⟨hx,hy⟩
  · exact Or.inl ⟨ha x hx,hb y hy⟩
  · exact Or.inr ⟨hb x hx,ha y hy⟩

/-- Inducing the selected host cannot increase actual common-neighbor
counts, so original-host branch mate-freeness survives without an Unmated
heredity claim. -/
theorem IsStarPacking.selected_host_mateFree [Fintype V] {G : SimpleGraph V}
    {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (_h : IsStarPacking G A C ell L) (q : ℝ)
    (hf : ∀ b ∈ C, MateFreeOn G q (insert b (L b:Set V))) :
    ∀ b ∈ selectedStarCenters C L,
      MateFreeOn (G.induce ((C ∪ C.biUnion L:Finset V):Set V)) q
        (insert b (selectedStarAssignment C L b:Set (SelectedStarVertex C L))) := by
  classical
  intro b hb x hx y hy hxy
  have hb' : b.val ∈ C := Finset.mem_subtype.mp hb
  have hx' : x.val ∈ insert b.val (L b.val:Set V) := by
    rcases hx with rfl|hx
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Finset.mem_subtype.mp hx)
  have hy' : y.val ∈ insert b.val (L b.val:Set V) := by
    rcases hy with rfl|hy
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Finset.mem_subtype.mp hy)
  let f : (G.induce ((C ∪ C.biUnion L:Finset V):Set V)).commonNeighbors x y →
      G.commonNeighbors x.val y.val := fun z => ⟨z.val.val,z.property⟩
  have hi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) hab))
  have hc := Fintype.card_le_of_injective f hi
  exact (Nat.cast_le.mpr hc).trans_lt
    (hf b.val hb' x.val hx' y.val hy' (fun he => hxy (Subtype.ext he)))

/-- The exact selected left/right ratio follows from disjoint full leaf
sets; it is not a size hypothesis on the original right side. -/
theorem IsStarPacking.selected_size_ratio {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hf : ∀ b ∈ C, (L b).card=ell) :
    (selectedStarLeaves C L).card=ell*(selectedStarCenters C L).card := by
  classical
  have hc : (selectedStarCenters C L).card=C.card := by
    rw [selectedStarCenters,Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr (fun _ hx => Finset.mem_union_left _ hx)
  have hl : (selectedStarLeaves C L).card=(C.biUnion L).card := by
    rw [selectedStarLeaves,Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr (fun _ hx => Finset.mem_union_right _ hx)
  rw [hc,hl,Finset.card_biUnion (fun b _ c _ hbc => h.2.2.2.2.1 b c hbc)]
  calc
    _ = ∑ _b ∈ C, ell := Finset.sum_congr rfl hf
    _ = _ := by simp [mul_comm]

end MinorFreeSpanners
