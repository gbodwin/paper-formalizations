import MinorFreeSpanners.StarPackingMinor

/-! Simultaneous actual star contraction retaining every unselected vertex
as a singleton branch. This supplies the graph/vertex-count interface;
quantitative edge-loss cleaning remains separate. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices not belonging to any selected star. -/
def starResidual (C : Finset V) (L : V → Finset V) : Finset V :=
  Finset.univ \ (C.biUnion fun b => insert b (L b))

/-- One label per selected star, plus every original residual vertex. -/
abbrev StarContractionVertex (C : Finset V) (L : V → Finset V) :=
  C ⊕ starResidual C L

/-- Explicit full partition into selected stars and residual singleton vertices. -/
def fullStarBranch (C : Finset V) (L : V → Finset V) :
    StarContractionVertex C L → Finset V
  | .inl b => insert b.val (L b.val)
  | .inr x => {x.val}

/-- The real simple quotient: loops suppressed and all parallel edges merged. -/
def fullStarContraction (G : SimpleGraph V) (C : Finset V) (L : V → Finset V) :
    SimpleGraph (StarContractionVertex C L) where
  Adj i j := i ≠ j ∧ ∃ x ∈ fullStarBranch C L i,
    ∃ y ∈ fullStarBranch C L j, G.Adj x y
  symm := ⟨by rintro i j ⟨hne,x,hx,y,hy,he⟩; exact ⟨hne.symm,y,hy,x,hx,he.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every original host vertex belongs to an actual quotient branch. -/
theorem fullStarBranch_cover (C : Finset V) (L : V → Finset V) (x : V) :
    ∃ i : StarContractionVertex C L, x ∈ fullStarBranch C L i := by
  classical
  by_cases hx : x ∈ C.biUnion (fun b => insert b (L b))
  · obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
    exact ⟨.inl ⟨b,hb⟩,hx⟩
  · exact ⟨.inr ⟨x,by simp [starResidual,hx]⟩,by simp [fullStarBranch]⟩

/-- Selected stars plus residual singleton branches are pairwise disjoint. -/
theorem IsStarPacking.fullBranch_disjoint {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (i j : StarContractionVertex C L) (hij : i ≠ j) :
    Disjoint (fullStarBranch C L i) (fullStarBranch C L j) := by
  classical
  cases i with
  | inl b =>
    cases j with
    | inl c =>
      exact h.branch_disjoint hAC b.property c.property
        (fun he => hij (congrArg Sum.inl (Subtype.ext he)))
    | inr x =>
      apply Finset.disjoint_left.mpr
      intro y hy hyx
      have he : y=x.val := by simpa [fullStarBranch] using hyx
      subst y
      exact (Finset.mem_sdiff.mp x.property).2
        (Finset.mem_biUnion.mpr ⟨b.val,b.property,hy⟩)
  | inr x =>
    cases j with
    | inl b =>
      apply Finset.disjoint_left.mpr
      intro y hyx hy
      have he : y=x.val := by simpa [fullStarBranch] using hyx
      subst y
      exact (Finset.mem_sdiff.mp x.property).2
        (Finset.mem_biUnion.mpr ⟨b.val,b.property,hy⟩)
    | inr y =>
      apply Finset.disjoint_singleton.mpr
      intro he
      exact hij (congrArg Sum.inr (Subtype.ext he))

/-- A full simultaneous contraction is an actual host minor. -/
def IsStarPacking.fullMinorModel {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : MinorModel (fullStarContraction G C L) G where
  branch i := (fullStarBranch C L i : Set V)
  nonempty := by intro i; cases i <;> simp [fullStarBranch]
  disjoint := fun i j hij => Finset.disjoint_coe.mpr (h.fullBranch_disjoint hAC i j hij)
  connected := by
    intro i x hx y hy
    cases i with
    | inl b =>
      obtain ⟨p,_,hp⟩ := h.branch_connected hx hy
      exact ⟨p,hp⟩
    | inr z =>
      have hx' : x=z.val := by simpa [fullStarBranch] using hx
      have hy' : y=z.val := by simpa [fullStarBranch] using hy
      subst x; subst y
      exact ⟨.nil,by simp [fullStarBranch]⟩
  adjacent := fun _ _ he => he.2

/-- Retaining singleton branches does not increase the star width bound. -/
theorem IsStarPacking.fullMinorModel_bounded {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : (h.fullMinorModel hAC).IsBounded (ell+1) := by
  classical
  intro i
  have he : ((h.fullMinorModel hAC).branch i).toFinset = fullStarBranch C L i := by
    ext x
    exact Set.mem_toFinset
  rw [he]
  cases i with
  | inl b =>
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (h.2.2.2.2.2 b.val) 1)
  | inr x => simp [fullStarBranch]

/-- Every branch of the full contraction is mate-free when the selected
stars are; all residual branches are literal singletons. -/
theorem IsStarPacking.fullMinorModel_mateFree {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) {q : ℝ}
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b:Set V))) :
    ∀ i, MateFreeOn G q ((h.fullMinorModel hAC).branch i) := by
  classical
  intro i
  cases i with
  | inl b =>
    simpa only [IsStarPacking.fullMinorModel,fullStarBranch,Finset.coe_insert] using hfree b.val b.property
  | inr z =>
    intro x hx y hy hxy
    have hx' : x=z.val := by simpa [IsStarPacking.fullMinorModel,fullStarBranch] using hx
    have hy' : y=z.val := by simpa [IsStarPacking.fullMinorModel,fullStarBranch] using hy
    exact (hxy (hx'.trans hy'.symm)).elim

/-- The full quotient loses exactly ell vertices per selected ell-leaf star. -/
theorem IsStarPacking.fullContraction_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (hfull : ∀ b ∈ C, (L b).card = ell) :
    Fintype.card (StarContractionVertex C L) + ell*C.card = Fintype.card V := by
  classical
  have hu := h.full_branch_union_card hAC hfull
  have hle : (ell+1)*C.card ≤ Fintype.card V := by
    rw [← hu]
    exact Finset.card_le_univ _
  have hr : (starResidual C L).card = Fintype.card V - (ell+1)*C.card := by
    rw [starResidual,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hu]
  change Fintype.card (C ⊕ starResidual C L) + ell*C.card = _
  rw [Fintype.card_sum,Fintype.card_coe,Fintype.card_coe,hr]
  simp only [Nat.add_mul,Nat.one_mul] at hle ⊢
  omega

end MinorFreeSpanners
