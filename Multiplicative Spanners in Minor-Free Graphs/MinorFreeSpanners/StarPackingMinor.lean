import MinorFreeSpanners.StarPackingSelection
import MinorFreeSpanners.BoundedMinor

/-! Actual disjoint induced-star branches and their simple quotient minor.
Loops are excluded and crossing edges are existentially merged. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Disjoint center and leaf domains give actual disjoint star branches. -/
theorem IsStarPacking.branch_disjoint {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) {b c : V} (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c) :
    Disjoint (insert b (L b)) (insert c (L c)) := by
  apply Finset.disjoint_left.mpr
  intro z hzb hzc
  rcases Finset.mem_insert.mp hzb with rfl|hzb <;>
    rcases Finset.mem_insert.mp hzc with he|hzc
  · exact hbc he
  · exact Finset.disjoint_left.mp hAC (h.2.1 c hzc) hb
  · subst z
    exact Finset.disjoint_left.mp hAC (h.2.1 b hzb) hc
  · exact Finset.disjoint_left.mp (h.2.2.2.2.1 b c hbc) hzb hzc

omit [Fintype V] in
/-- Each vertex in a star has a literal zero- or one-edge walk to its center. -/
theorem IsStarPacking.walk_to_center {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    {b u : V} (hu : u ∈ insert b (L b)) :
    ∃ p : G.Walk u b, p.length ≤ 1 ∧ ∀ z ∈ p.support, z ∈ insert b (L b) := by
  rcases Finset.mem_insert.mp hu with rfl|hu
  · exact ⟨.nil,by simp,by simp⟩
  · refine ⟨.cons (h.2.2.1 b u hu).symm .nil,by simp,?_⟩
    intro z hz
    simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> simp [hu]

omit [Fintype V] in
/-- Star connectivity is witnessed by an actual internal walk of length at most two. -/
theorem IsStarPacking.branch_connected {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    {b u v : V} (hu : u ∈ insert b (L b)) (hv : v ∈ insert b (L b)) :
    ∃ p : G.Walk u v, p.length ≤ 2 ∧ ∀ z ∈ p.support, z ∈ insert b (L b) := by
  obtain ⟨p,hp,hps⟩ := h.walk_to_center hu
  obtain ⟨q,hq,hqs⟩ := h.walk_to_center hv
  refine ⟨p.append q.reverse,?_,?_⟩
  · simp only [Walk.length_append,Walk.length_reverse]; omega
  · intro z hz
    have hz' := (Walk.mem_support_append_iff p q.reverse).mp hz
    rcases hz' with hz'|hz'
    · exact hps z hz'
    · exact hqs z (by simpa using hz')

omit [Fintype V] in
/-- The induced host graph on one branch is exactly its center-leaf star. -/
theorem IsStarPacking.branch_adj_iff {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    {b u v : V} (hu : u ∈ insert b (L b)) (hv : v ∈ insert b (L b)) :
    G.Adj u v ↔ (u=b ∧ v ∈ L b) ∨ (v=b ∧ u ∈ L b) := by
  constructor
  · intro he
    rcases Finset.mem_insert.mp hu with rfl|hu <;>
      rcases Finset.mem_insert.mp hv with rfl|hv
    · exact (he.ne rfl).elim
    · exact Or.inl ⟨rfl,hv⟩
    · exact Or.inr ⟨rfl,hu⟩
    · exact (h.2.2.2.1 b u hu v hv he.ne he).elim
  · rintro (⟨rfl,hv⟩|⟨rfl,hu⟩)
    · exact h.2.2.1 _ _ hv
    · exact (h.2.2.1 _ _ hu).symm

omit [Fintype V] in
/-- The literal selected vertex union has (ell+1) vertices per full star. -/
theorem IsStarPacking.full_branch_union_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (hfull : ∀ b ∈ C, (L b).card = ell) :
    (C.biUnion fun b => insert b (L b)).card = (ell+1)*C.card := by
  classical
  rw [Finset.card_biUnion (fun b hb c hc hbc => h.branch_disjoint hAC hb hc hbc)]
  calc
    _ = ∑ b ∈ C, (ell+1) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hnot : b ∉ L b := fun hmem => (h.2.2.1 b b hmem).ne rfl
      rw [Finset.card_insert_of_notMem hnot,hfull b hb]
    _ = _ := by simp [Nat.mul_comm]

/-- The actual simple quotient graph of a finite star family. -/
def starPackingQuotient (G : SimpleGraph V) (C : Finset V) (L : V → Finset V) :
    SimpleGraph C where
  Adj b c := b ≠ c ∧ ∃ u ∈ insert b.val (L b.val),
    ∃ v ∈ insert c.val (L c.val), G.Adj u v
  symm := ⟨by rintro b c ⟨hne,u,hu,v,hv,he⟩; exact ⟨hne.symm,v,hv,u,hu,he.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The quotient comes with an explicit host minor model, not a certificate input. -/
def IsStarPacking.minorModel {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : MinorModel (starPackingQuotient G C L) G where
  branch b := (insert b.val (L b.val) : Finset V)
  nonempty b := ⟨b.val,by simp⟩
  disjoint := by
    intro b c hbc
    exact Finset.disjoint_coe.mpr (h.branch_disjoint hAC b.property c.property
      (fun he => hbc (Subtype.ext he)))
  connected := by
    intro b u hu v hv
    obtain ⟨p,_,hp⟩ := h.branch_connected hu hv
    exact ⟨p,hp⟩
  adjacent := fun _ _ he => he.2

/-- The actual branch width is at most the leaf bound plus its one center. -/
theorem IsStarPacking.minorModel_bounded {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : (h.minorModel hAC).IsBounded (ell+1) := by
  classical
  intro b
  have he : ((h.minorModel hAC).branch b).toFinset = insert b.val (L b.val) := by
    ext x
    simp [IsStarPacking.minorModel]
  rw [he]
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (h.2.2.2.2.2 b.val) 1)

/-- The complete actual full-star family and bounded quotient minor supplied
by the degree assumptions. The input includes no packing or minor oracle. -/
theorem exists_full_star_minor (G : SimpleGraph V) (A B : Finset V)
    (ell dA dB : ℕ) (hAB : Disjoint A B)
    (hsize : ell*B.card ≤ A.card) (hdeg : dA < dB)
    (hA : ∀ x ∈ A, (A.filter fun z => G.Adj x z).card ≤ dA)
    (hB : ∀ x ∈ A, dB ≤ (B.filter fun b => G.Adj x b).card) :
    ∃ C : Finset V, ∃ L : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell L ∧
      (∀ b ∈ C, (L b).card = ell) ∧
      (∀ w ∈ C.biUnion L, ((B \ C).filter fun b => G.Adj w b).card ≤ dA) ∧
      (A.Nonempty → C.Nonempty) ∧
      (C.biUnion fun b => insert b (L b)).card = (ell+1)*C.card ∧
      ∃ M : MinorModel (starPackingQuotient G C L) G, M.IsBounded (ell+1) := by
  classical
  obtain ⟨C,L,hCB,hL,hfull,hboundary,hne⟩ :=
    exists_full_star_selection G A B ell dA dB hsize hdeg hA hB
  have hAC : Disjoint A C := hAB.mono_right hCB
  exact ⟨C,L,hCB,hL,hfull,hboundary,hne,hL.full_branch_union_card hAC hfull,
    hL.minorModel hAC,hL.minorModel_bounded hAC⟩

end MinorFreeSpanners
