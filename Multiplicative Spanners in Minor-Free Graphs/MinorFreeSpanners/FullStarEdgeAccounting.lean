import MinorFreeSpanners.SimpleQuotientCount

/-! Exact simultaneous star contraction accounting on the actual full
simple quotient. Cleaning of crossing fibers is a separate remaining step. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Assign every host vertex to one actual branch of the covering star family. -/
noncomputable def fullStarLabel (C : Finset V) (L : V → Finset V)
    (x : V) : StarContractionVertex C L := (fullStarBranch_cover C L x).choose

theorem fullStarLabel_mem (C : Finset V) (L : V → Finset V) (x : V) :
    x ∈ fullStarBranch C L (fullStarLabel C L x) :=
  (fullStarBranch_cover C L x).choose_spec

/-- Disjointness makes the chosen branch label exact. -/
theorem IsStarPacking.fullStarLabel_eq_iff {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (x : V) (i : StarContractionVertex C L) :
    fullStarLabel C L x = i ↔ x ∈ fullStarBranch C L i := by
  constructor
  · intro he
    exact he ▸ fullStarLabel_mem C L x
  · intro hx
    by_contra hn
    exact Finset.disjoint_left.mp (h.fullBranch_disjoint hAC _ _ hn)
      (fullStarLabel_mem C L x) hx

/-- The branch-defined full quotient is literally the simple graph map by
its proved covering branch labels. -/
theorem IsStarPacking.fullContraction_eq_map {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) :
    fullStarContraction G C L = G.map (fullStarLabel C L) := by
  ext i j
  change (i ≠ j ∧ ∃ x ∈ fullStarBranch C L i,
    ∃ y ∈ fullStarBranch C L j, G.Adj x y) ↔ _
  rw [map_adj']
  constructor
  · rintro ⟨hne,x,hx,y,hy,he⟩
    exact ⟨hne,x,y,he,(h.fullStarLabel_eq_iff hAC x i).mpr hx,
      (h.fullStarLabel_eq_iff hAC y j).mpr hy⟩
  · rintro ⟨hne,x,y,he,hx,hy⟩
    exact ⟨hne,x,(h.fullStarLabel_eq_iff hAC x i).mp hx,
      y,(h.fullStarLabel_eq_iff hAC y j).mp hy,he⟩

/-- Literal center-leaf forest edges of the selected star family. -/
def starForestEdges (C : Finset V) (L : V → Finset V) : Finset (Sym2 V) :=
  C.biUnion fun b => (L b).image fun x => s(b,x)

/-- The internal edges removed by simultaneous contraction are exactly the
actual selected star edges; no additional chord is silently discarded. -/
theorem IsStarPacking.internalEdges_eq_starForest {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) :
    quotientInternalEdges G (fullStarLabel C L) = starForestEdges C L := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [quotientInternalEdges,Finset.mem_filter,mem_edgeFinset,
      Sym2.map_mk,Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨he,hlab⟩
      have hx := fullStarLabel_mem C L x
      have hy := fullStarLabel_mem C L y
      rw [← hlab] at hy
      cases hi : fullStarLabel C L x with
      | inl b =>
        rw [hi] at hx hy
        obtain ⟨rfl,hy⟩|⟨rfl,hx⟩ := (h.branch_adj_iff hx hy).mp he
        · exact Finset.mem_biUnion.mpr ⟨b.val,b.property,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨b.val,b.property,
            Finset.mem_image.mpr ⟨x,hx,Sym2.eq_swap⟩⟩
      | inr z =>
        rw [hi] at hx hy
        have hx' : x=z.val := by simpa [fullStarBranch] using hx
        have hy' : y=z.val := by simpa [fullStarBranch] using hy
        exact (he.ne (hx'.trans hy'.symm)).elim
    · intro hm
      obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp he
      have hlb := (h.fullStarLabel_eq_iff hAC b (.inl ⟨b,hb⟩)).mpr
        (show b ∈ fullStarBranch C L (.inl ⟨b,hb⟩) by simp [fullStarBranch])
      have hlz := (h.fullStarLabel_eq_iff hAC z (.inl ⟨b,hb⟩)).mpr
        (show z ∈ fullStarBranch C L (.inl ⟨b,hb⟩) by simp [fullStarBranch,hz])
      have hboth : G.Adj b z ∧ fullStarLabel C L b = fullStarLabel C L z :=
        ⟨h.2.2.1 b z hz,hlb.trans hlz.symm⟩
      have hout : s(b,z) ∈ quotientInternalEdges G (fullStarLabel C L) := by
        simpa [quotientInternalEdges] using hboth
      have hout' : s(x,y) ∈ quotientInternalEdges G (fullStarLabel C L) := heq ▸ hout
      simpa [quotientInternalEdges] using hout'

omit [Fintype V] in
/-- Distinct selected stars have disjoint actual edge sets. -/
theorem IsStarPacking.starForest_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (hfull : ∀ b ∈ C, (L b).card = ell) :
    (starForestEdges C L).card = ell*C.card := by
  classical
  have hd : ∀ b ∈ C, ∀ c ∈ C, b ≠ c →
      Disjoint ((L b).image fun x => s(b,x)) ((L c).image fun x => s(c,x)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hf
    rcases Sym2.eq_iff.mp hxy with ⟨he,_⟩|⟨_,he⟩
    · exact hbc he.symm
    · exact Finset.disjoint_left.mp hAC (he ▸ h.2.1 c hy) hb
  rw [starForestEdges,Finset.card_biUnion hd]
  calc
    _ = ∑ b ∈ C, ell := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.card_image_of_injective]
      · exact hfull b hb
      · intro x y he
        rcases Sym2.eq_iff.mp he with ⟨_,he⟩|⟨h1,h2⟩
        · exact he
        · exact h2.trans h1
    _ = ell*C.card := by simp [Nat.mul_comm]

/-- Exact edge-loss identity for the actual full simultaneous contraction.
The remaining crossing-fiber surplus is explicit, not bounded by a hidden
cleaning assumption. -/
theorem IsStarPacking.fullContraction_edge_loss {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (hfull : ∀ b ∈ C, (L b).card = ell) :
    (fullStarContraction G C L).edgeFinset.card + ell*C.card +
      ∑ q ∈ (fullStarContraction G C L).edgeFinset,
        (((quotientCrossEdges G (fullStarLabel C L)).filter
          fun e => Sym2.map (fullStarLabel C L) e = q).card - 1) = G.edgeFinset.card := by
  classical
  have he := quotient_edge_loss G (fullStarLabel C L)
  rw [h.internalEdges_eq_starForest hAC,h.starForest_card hAC hfull] at he
  have hfs : (fullStarContraction G C L).edgeFinset =
      (G.map (fullStarLabel C L)).edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr (h.fullContraction_eq_map hAC)
  simpa only [hfs] using he

end MinorFreeSpanners
