import LightEFTSpanners.SubdivisionPreserver
import LightEFTSpanners.PotentialForcing

/-! Actual failed subdivision edges and a lifted potential force a core edge.
The remaining cycle step supplies the base potential; no spanner lower bound is
assumed here. -/
namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset LightSpanners
variable {V I : Type*} [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

noncomputable def coreWeight (W : ℝ) (e : Sym2 (Vertex (I:=I) C)) : ℝ :=
  if e∈(coreGraph C C).edgeSet then W else 1

noncomputable def edgeMidpoint (φ : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => (φ a+φ b)/2,by intro a b; dsimp; rw [add_comm]⟩

noncomputable def endpointFaults {u v : V} (huv : C.Adj u v) :
    Finset (Sym2 (Vertex (I:=I) C)) :=
  univ.image (fun j => s(Sum.inl u,Sum.inr (⟨s(u,v),(mem_edgeSet C).mpr huv⟩,j)))

noncomputable def cutPotential {u v : V} (_huv : C.Adj u v) (φ : V → ℝ) :
    Vertex (I:=I) C → ℝ
  | Sum.inl a => φ a
  | Sum.inr z => if (z.1:Sym2 V)=s(u,v) then φ v else edgeMidpoint φ z.1

theorem endpointFaults_card {u v : V} (huv : C.Adj u v) :
    (endpointFaults (I:=I) C huv).card≤Fintype.card I := by
  classical
  exact card_image_le.trans_eq (card_univ)

/-- A base potential with jumps at most two off the removed base edge extends
to a unit-Lipschitz potential on every surviving subdivision edge. -/
theorem cutPotential_cross {u v : V} (huv : C.Adj u v) (φ : V → ℝ)
    (hφ : ∀ a b,(C.deleteEdges {s(u,v)}).Adj a b → |φ b-φ a|≤2)
    (a : V) (z : C.edgeSet×I) (ha : a∈(z.1:Sym2 V))
    (hn : s(Sum.inl a,Sum.inr z)∉endpointFaults C huv) :
    |cutPotential C huv φ (Sum.inr z)-φ a|≤1 := by
  classical
  by_cases hz : (z.1:Sym2 V)=s(u,v)
  · have haz : a=u ∨ a=v := by simpa only [hz,Sym2.mem_iff] using ha
    have hne : a≠u := by
      intro heq
      apply hn
      apply mem_image.mpr
      refine ⟨z.2,mem_univ _,?_⟩
      have hd : (⟨s(u,v),(mem_edgeSet C).mpr huv⟩ : C.edgeSet)=z.1 := Subtype.ext hz.symm
      simp [heq,hd]
    have hav := haz.resolve_left hne
    simp [cutPotential,hz,hav]
  · obtain ⟨b,he⟩ := Sym2.mem_iff_exists.mp ha
    have hab : C.Adj a b := (mem_edgeSet C).mp (he ▸ z.1.property)
    have hbound := hφ a b (deleteEdges_adj.mpr ⟨hab,by simpa [← he] using hz⟩)
    rw [abs_le] at hbound ⊢
    simp only [cutPotential,ite_eq_right hz]
    simp only [edgeMidpoint,he,Sym2.lift_mk]
    constructor <;> linarith

/-- With one failed edge per subdivision branch, any EFT spanner must retain
the removed core edge whenever its potential gap exceeds the requested stretch. -/
theorem core_edge_forced {u v : V} (huv : C.Adj u v)
    (W t : ℝ) (hW : 2≤W) (φ : V → ℝ)
    (hφ : ∀ a b,(C.deleteEdges {s(u,v)}).Adj a b → |φ b-φ a|≤2)
    (hgap : t*W<φ v-φ u)
    (H : SimpleGraph (Vertex (I:=I) C))
    (hH : IsEFTSpanner (graph C ⊔ coreGraph C C) H (coreWeight C W) t
      (Fintype.card I)) : H.Adj (Sum.inl u) (Sum.inl v) := by
  classical
  let F := endpointFaults (I:=I) C huv
  have hedge : (graph (I:=I) C ⊔ coreGraph C C).Adj (Sum.inl u) (Sum.inl v) := Or.inr huv
  have hwcore {a b : V} (hab : C.Adj a b) :
      coreWeight (I:=I) C W s(Sum.inl a,Sum.inl b)=W := by
    simp [coreWeight,mem_edgeSet,coreGraph,hab]
  apply eft_edge_forced_by_fault_potential hH hedge F (endpointFaults_card C huv)
    (φ := cutPotential C huv φ)
  · intro he
    obtain ⟨j,_,he⟩ := mem_image.mp he
    rcases Sym2.eq_iff.mp he with he | he <;> cases he.2
  · intro a b hab
    obtain ⟨hab,hebad⟩ := deleteEdges_adj.mp hab
    obtain ⟨hab,heF⟩ := deleteEdges_adj.mp hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hbase : C.Adj a b := hab.resolve_left (by simp [graph])
        have hne : s(a,b)≠s(u,v) := by
          intro heq
          apply hebad
          apply Set.mem_singleton_iff.mpr
          exact congrArg (Sym2.map Sum.inl) heq
        have hbound := hφ a b (deleteEdges_adj.mpr ⟨hbase,by simpa using hne⟩)
        simpa only [cutPotential,hwcore hbase] using
          (le_abs_self (φ b-φ a)).trans (hbound.trans hW)
      | inr z =>
        have hbase : a∈(z.1:Sym2 V) := hab.resolve_right (by simp [coreGraph])
        have hbound := cutPotential_cross C huv φ hφ a z hbase heF
        simpa [coreWeight,mem_edgeSet,coreGraph,cutPotential] using
          (le_abs_self (cutPotential C huv φ (Sum.inr z)-φ a)).trans hbound
    | inr z =>
      cases b with
      | inl b =>
        have hbase : b∈(z.1:Sym2 V) := hab.resolve_right (by simp [coreGraph])
        have hnot : s(Sum.inl b,Sum.inr z)∉F := by simpa only [Sym2.eq_swap,Finset.mem_coe] using heF
        have hbound := cutPotential_cross C huv φ hφ b z hbase hnot
        have hh : φ b-cutPotential C huv φ (Sum.inr z)≤1 :=
          (le_abs_self _).trans (by simpa only [abs_sub_comm] using hbound)
        simpa [coreWeight,mem_edgeSet,coreGraph,cutPotential] using hh
      | inr z' => exact False.elim (hab.elim id id)
  · simpa only [cutPotential,hwcore huv] using hgap

end LightEFTSpanners.ParallelSubdivision
