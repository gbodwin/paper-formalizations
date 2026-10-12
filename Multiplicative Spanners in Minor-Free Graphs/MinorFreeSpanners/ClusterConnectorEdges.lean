import MinorFreeSpanners.ClusterEdgeWeights
import MinorFreeSpanners.ConnectedSetUnitCredits

/-! Choose distinct actual host bridges for distinct coarse edges. These
identities are fresh relative to every edge internal to an old cluster. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

noncomputable def crossingEmbedding (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) : (C.graph T).edgeSet ↪ T.edgeSet where
  toFun e := ⟨(C.exists_crossing_edge hA hT e.val e.property).choose,
    (C.exists_crossing_edge hA hT e.val e.property).choose_spec.1⟩
  inj' := by
    intro e f he
    apply Subtype.ext
    apply Sym2.map.injective (@Option.some_injective I)
    have heq := congrArg (fun d : T.edgeSet => Sym2.map (C.minorModel hA hT).branchLabel d.val) he
    exact (C.exists_crossing_edge hA hT e.val e.property).choose_spec.2.symm.trans
      (heq.trans (C.exists_crossing_edge hA hT f.val f.property).choose_spec.2)

lemma crossingEmbedding_label (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (e : (C.graph T).edgeSet) :
    Sym2.map (C.minorModel hA hT).branchLabel (C.crossingEmbedding hA hT e).val =
      Sym2.map some e.val :=
  (C.exists_crossing_edge hA hT e.val e.property).choose_spec.2

lemma crossingEmbedding_not_internal (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (e : (C.graph T).edgeSet) (i : I)
    (x y : V) (hx : x∈C.branch i) (hy : y∈C.branch i) :
    (C.crossingEmbedding hA hT e).val ≠ s(x,y) := by
  intro he
  have hl := C.crossingEmbedding_label hA hT e
  rw [he] at hl
  simp only [Sym2.map_mk,(C.minorModel hA hT).branchLabel_eq hx,
    (C.minorModel hA hT).branchLabel_eq hy] at hl
  have hd : (Sym2.map some e.val).IsDiag := by rw [← hl]; exact Sym2.mk_isDiag_iff.mpr rfl
  have hd' := (Sym2.isDiag_map (@Option.some_injective I)).mp hd
  exact (C.graph T).not_isDiag_of_mem_edgeSet e.property hd'

end ClusterFamily
end MinorFreeSpanners
