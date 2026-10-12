import MinorFreeSpanners.ActualGroupReindex
import MinorFreeSpanners.WeightedHighDegreePhase

/-! Call the actual high-degree selection and retain its original groups,
low-degree remainder, literal half-credit and marked-edge bill under the
same group indexing consumed by the mixed-phase ledger. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

theorem exists_indexed_high_degree_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D M L g : ℝ}
    (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G)
    (hD : 0≤D) (hM : 0≤M) (hL : 0<L)
    (hweight : ∀ e∈B.edgeSet, w e ≤ M)
    (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet, 0≤w e)
    (hlight : ∀ e∈A.edgeSet, w e < L) (hheavy : ∀ e∈B.edgeSet, L≤w e)
    (r h : ℕ) (hr : 1≤r) (hh : 0<h) (hfree : CliqueMinorFree G h)
    (hgeometry : ((2*r:ℕ):ℝ)*(1+D/L) ≤ g)
    (q : ℕ) (credit : I → ℝ) (b R : ℝ) (hb : 0≤b)
    (hc : ∀ i, b ≤ credit i)
    (hreserve : 2*R ≤ (q+1:ℕ)*b)
    (hpay : 2*(2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*M ≤ b) :
    ∃ P : Finset (Finset I),
    ∃ F : ClusterFamily (I:={S // S∈P}) G w (4*(D+M)+D),
      (∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ i,i∉P.biUnion id → (C.graph B).degree i<q) ∧
      (∀ S : {S // S∈P},q+1≤S.val.card ∧ R≤(∑ i∈S.val,credit i)/2) ∧
      (∑ e∈C.markedEdges B (P.biUnion id),w e)+
        (∑ S : {S // S∈P},(∑ i∈S.val,credit i)/2)≤∑ i∈P.biUnion id,credit i := by
  classical
  obtain ⟨centers,groups,F,_,hsize,hbranch,hlow,hkeep,hpaid⟩ :=
    exists_weighted_high_degree_phase C hA hB hD hM hL hweight hG hw hlight hheavy
      r h hr hh hfree hgeometry q credit b R hb hc hreserve hpay
  let groups' : {c // c∈centers} → Finset I := fun c => groups c.val
  let P : Finset (Finset I) := Finset.univ.image groups'
  let e := C.originalGroupEquiv F groups' hbranch
  let F' := F.reindex e.symm
  have hU : P.biUnion id=centers.biUnion groups := by
    ext i
    simp [P,groups']
  have he (S : {S // S∈P}) : groups (e.symm S).val=S.val :=
    congrArg Subtype.val (e.apply_symm_apply S)
  have hsum : (∑ S : {S // S∈P},(∑ i∈S.val,credit i)/2)=
      ∑ c∈centers,(∑ i∈groups c,credit i)/2 := by
    have hh := e.sum_comp (fun S => (∑ i∈S.val,credit i)/2)
    change (∑ c : {c // c∈centers},(∑ i∈groups c.val,credit i)/2)=_ at hh
    exact hh.symm.trans (Finset.sum_coe_sort centers (fun c => (∑ i∈groups c,credit i)/2))
  refine ⟨P,F',fun S => C.reindexed_group_branch F groups' hbranch S,?_,?_,?_⟩
  · intro i hi
    rw [hU] at hi
    exact hlow i hi
  · intro S
    constructor
    · simpa only [he S] using hsize (e.symm S).val (e.symm S).property
    · simpa only [he S] using hkeep (e.symm S).val (e.symm S).property
  · rw [hsum,hU]
    exact hpaid

end MinorFreeSpanners
