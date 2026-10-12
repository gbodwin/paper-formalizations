import MinorFreeSpanners.ConstructedRetainedCreditFamily

/-! A finite next-level state retains the exact new connector set and its
whole prior history. Reindexing only changes cluster names; actual host carriers,
pointwise credit and the complete payment ledger are preserved. Intrinsic metric
certificates are tightened by the already proved uniform cap without increasing
any credit demand. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype V] {A G T B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

noncomputable def FiniteRetainedPhaseOutput (C : ClusterFamily (I:=I) A w D) (G T B : SimpleGraph V) (cap c baseline initial : ℝ) (prior : Finset (Sym2 V)) : Prop :=
  ∃ fresh : Finset (Sym2 V),Disjoint prior fresh ∧
    (∀ e∈prior∪fresh,e∈T.edgeSet) ∧
    ∃ n : ℕ,∃ next : ClusterFamily (I:=Fin n) G w cap,
    ∃ radius keep : Fin n → ℝ,
      (∀ x,∃ j,x∈next.branch j) ∧
      (∀ i,∃ j,C.branch i⊆next.branch j) ∧
      (∀ j,radius j≤cap) ∧
      (∀ j,∀ x∈next.branch j,∀ y∈next.branch j,
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈next.branch j) ∧ walkWeight w p≤radius j) ∧
      (∀ j,c*max (radius j) baseline≤keep j) ∧ (∀ j,0≤keep j) ∧
      (∀ e∈prior∪fresh,∃ j x y,x∈next.branch j ∧ y∈next.branch j ∧ e=s(x,y)) ∧
      (∑ e∈B.edgeFinset,w e)+(∑ j,keep j)≤ initial+c*(∑ e∈prior∪fresh,w e)

omit [Fintype V] in
 theorem ClusterFamily.coarsens_of_union {J : Type*}
    (C : ClusterFamily (I:=I) A w D) {cap : ℝ} (F : ClusterFamily (I:=J) G w cap)
    (groups : J → Finset I) (hbranch : ∀ j,F.branch j={x | ∃ i∈groups j,x∈C.branch i})
    (hcover : ∀ x,∃ j,x∈F.branch j) : ∀ i,∃ j,C.branch i⊆F.branch j := by
  intro i
  obtain ⟨x,hx⟩ := C.nonempty i
  obtain ⟨j,hj⟩ := hcover x
  rw [hbranch] at hj
  obtain ⟨k,hk,hxk⟩ := hj
  have he : i=k := by
    by_contra hne
    exact Set.disjoint_left.mp (C.disjoint i k hne) hx hxk
  subst k
  refine ⟨j,?_⟩
  intro y hy
  rw [hbranch]
  exact ⟨i,hk,hy⟩

 theorem finite_retained_phase_of_family {J : Type*} [Fintype J]
    {cap c baseline initial : ℝ} (C : ClusterFamily (I:=I) A w D) (F : ClusterFamily (I:=J) G w cap)
    (radius keep : J → ℝ) (prior fresh : Finset (Sym2 V))
    (hcover : ∀ x,∃ j,x∈F.branch j) (hcoarse : ∀ i,∃ j,C.branch i⊆F.branch j)
    (hwalk : ∀ j,∀ x∈F.branch j,∀ y∈F.branch j,
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch j) ∧ walkWeight w p≤radius j)
    (hc : 0≤c) (hkeep : ∀ j,c*max (radius j) baseline≤keep j) (hkeep0 : ∀ j,0≤keep j)
    (hdis : Disjoint prior fresh) (htree : ∀ e∈prior∪fresh,e∈T.edgeSet)
    (hint : ∀ e∈prior∪fresh,∃ j x y,x∈F.branch j ∧ y∈F.branch j ∧ e=s(x,y))
    (hpaid : (∑ e∈B.edgeFinset,w e)+(∑ j,keep j)≤ initial+c*(∑ e∈prior∪fresh,w e)) :
    FiniteRetainedPhaseOutput C G T B cap c baseline initial prior := by
  classical
  let e := Fintype.equivFin J
  refine ⟨fresh,hdis,htree,Fintype.card J,F.reindex e.symm,(fun j => min (radius (e.symm j)) cap),keep∘e.symm,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    obtain ⟨j,hj⟩ := hcover x
    exact ⟨e j,by simpa [ClusterFamily.reindex] using hj⟩
  · intro i
    obtain ⟨j,hj⟩ := hcoarse i
    exact ⟨e j,by simpa [ClusterFamily.reindex] using hj⟩
  · exact fun j => min_le_right _ _
  · intro j x hx y hy
    by_cases hr : radius (e.symm j)≤cap
    · simpa only [min_eq_left hr,ClusterFamily.reindex] using hwalk (e.symm j) x hx y hy
    · simpa only [min_eq_right (le_of_not_ge hr),ClusterFamily.reindex] using F.connected (e.symm j) x hx y hy
  · intro j
    exact (mul_le_mul_of_nonneg_left (max_le_max_right baseline (min_le_left _ _)) hc).trans (hkeep (e.symm j))
  · exact fun j => hkeep0 (e.symm j)
  · intro f hf
    obtain ⟨j,x,y,hx,hy,he⟩ := hint f hf
    exact ⟨e j,x,y,by simpa [ClusterFamily.reindex] using hx,
      by simpa [ClusterFamily.reindex] using hy,he⟩
  · have hs : (∑ j : Fin (Fintype.card J),keep (e.symm j))=∑ j,keep j :=
      e.symm.sum_comp keep
    simpa only [Function.comp_apply,hs] using hpaid

end MinorFreeSpanners
