import MinorFreeSpanners.FullStarContraction
import MinorFreeSpanners.FullContractionModel

/-! General host stars may have extra edges among their leaves. Only the
selected star edges form a forest; the full simple quotient retains all
crossing host edges. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact size-k disjoint actual stars, without an induced-claw premise. -/
def IsGeneralStarForest (G : SimpleGraph V) (k : ℕ) (C : Finset V)
    (L : V → Finset V) : Prop :=
  (∀ c ∈ C, ∀ x ∈ L c, G.Adj c x) ∧
  (∀ c ∈ C, (insert c (L c)).card=k) ∧
  ∀ c ∈ C, ∀ b ∈ C, c ≠ b → Disjoint (insert c (L c)) (insert b (L b))

omit [Fintype V] in
theorem empty_general_star_forest (G : SimpleGraph V) (k : ℕ) :
    IsGeneralStarForest G k ∅ (fun _ => ∅) := by
  simp [IsGeneralStarForest]

omit [Fintype V] in
theorem IsGeneralStarForest.walk_to_center {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L)
    {c x : V} (hc : c ∈ C) (hx : x ∈ insert c (L c)) :
    ∃ p : G.Walk x c, ∀ y ∈ p.support, y ∈ insert c (L c) := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨.nil,by simp⟩
  · refine ⟨.cons (h.1 c hc x hx).symm .nil,?_⟩
    intro y hy
    simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl <;> simp [hx]

theorem IsGeneralStarForest.fullBranch_disjoint {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L)
    (i j : StarContractionVertex C L) (hij : i ≠ j) :
    Disjoint (fullStarBranch C L i) (fullStarBranch C L j) := by
  cases i with
  | inl b =>
    cases j with
    | inl c =>
      exact h.2.2 b.val b.property c.val c.property
        (fun he => hij (congrArg Sum.inl (Subtype.ext he)))
    | inr x =>
      apply Finset.disjoint_left.mpr
      intro y hy hyx
      have he : y=x.val := by simpa [fullStarBranch] using hyx
      subst y
      exact (Finset.mem_sdiff.mp x.property).2 (Finset.mem_biUnion.mpr ⟨b.val,b.property,hy⟩)
  | inr x =>
    cases j with
    | inl b =>
      apply Finset.disjoint_left.mpr
      intro y hyx hy
      have he : y=x.val := by simpa [fullStarBranch] using hyx
      subst y
      exact (Finset.mem_sdiff.mp x.property).2 (Finset.mem_biUnion.mpr ⟨b.val,b.property,hy⟩)
    | inr y =>
      apply Finset.disjoint_singleton.mpr
      intro he
      exact hij (congrArg Sum.inr (Subtype.ext he))

/-- An actual full covering host-minor model for the literal quotient. -/
def IsGeneralStarForest.fullMinorModel {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L) :
    MinorModel (fullStarContraction G C L) G where
  branch i := (fullStarBranch C L i:Set V)
  nonempty := by intro i;cases i <;> simp [fullStarBranch]
  disjoint := fun i j hij => Finset.disjoint_coe.mpr (h.fullBranch_disjoint i j hij)
  connected := by
    intro i x hx y hy
    cases i with
    | inl c =>
      obtain ⟨p,hp⟩ := h.walk_to_center c.property hx
      obtain ⟨q,hq⟩ := h.walk_to_center c.property hy
      refine ⟨p.append q.reverse,?_⟩
      intro z hz
      rcases (Walk.mem_support_append_iff p q.reverse).mp hz with hz | hz
      · exact hp z hz
      · exact hq z (by simpa using hz)
    | inr c =>
      have hx' : x=c.val := by simpa [fullStarBranch] using hx
      have hy' : y=c.val := by simpa [fullStarBranch] using hy
      subst x;subst y
      exact ⟨.nil,by simp [fullStarBranch]⟩
  adjacent := fun _ _ he => he.2

theorem IsGeneralStarForest.fullMinorModel_covers {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L) :
    h.fullMinorModel.Covers := fullStarBranch_cover C L

theorem IsGeneralStarForest.fullMinorModel_full {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L) :
    h.fullMinorModel.IsFull := by
  intro i j hij x hx y hy he
  exact ⟨hij,x,hx,y,hy,he⟩

theorem IsGeneralStarForest.fullMinorModel_bounded {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L) (hk : 1 ≤ k) :
    h.fullMinorModel.IsBounded k := by
  intro i
  have he : (h.fullMinorModel.branch i).toFinset=fullStarBranch C L i := by
    ext x
    exact Set.mem_toFinset
  rw [he]
  cases i with
  | inl c => exact (h.2.1 c.val c.property).le
  | inr x => simpa [fullStarBranch] using hk

omit [Fintype V] in
/-- Every original selected star has exactly k vertices and no overlaps. -/
theorem IsGeneralStarForest.covered_card {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L) :
    (C.biUnion (fun c => insert c (L c))).card=k*C.card := by
  rw [Finset.card_biUnion (fun c hc b hb hcb => h.2.2 c hc b hb hcb)]
  simp_rw [Finset.sum_congr rfl (fun c hc => h.2.1 c hc)]
  simp [Nat.mul_comm]

theorem IsGeneralStarForest.quotient_card {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L) (hk : 1 ≤ k) :
    Fintype.card (StarContractionVertex C L)+(k-1)*C.card=Fintype.card V := by
  have hc := h.covered_card
  have hle : k*C.card ≤ Fintype.card V := by rw [← hc];exact Finset.card_le_univ _
  have hr : (starResidual C L).card=Fintype.card V-k*C.card := by
    rw [starResidual,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hc]
  change Fintype.card (C ⊕ starResidual C L)+(k-1)*C.card=_
  rw [Fintype.card_sum,Fintype.card_coe,Fintype.card_coe,hr]
  have hm : (k-1)*C.card+C.card=k*C.card := by
    calc
      _ = ((k-1)+1)*C.card := by ring
      _ = _ := by rw [Nat.sub_add_cancel hk]
  omega

end MinorFreeSpanners
