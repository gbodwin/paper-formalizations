import LightEFTSpanners.ParallelSubdivision
import LightSpanners.Weight
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset LightSpanners
variable {V I : Type*} [Fintype V] [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

def dartEdge (d : C.Dart) (j : I) : Sym2 (Vertex (I:=I) C) :=
  s(Sum.inl d.fst,Sum.inr (⟨d.edge,d.edge_mem⟩,j))

omit [Fintype V] in
theorem exists_dart_at_endpoint (e : C.edgeSet) (a : V) (ha : a∈(e:Sym2 V)) :
    ∃ d : C.Dart,d.fst=a ∧ d.edge=e := by
  obtain ⟨b,he⟩ := Sym2.mem_iff_exists.mp ha
  have hab : C.Adj a b := (mem_edgeSet C).mp (he ▸ e.property)
  exact ⟨⟨(a,b),hab⟩,rfl,he.symm⟩

theorem edgeFinset_subset_dart_image :
    (graph (I:=I) C).edgeFinset ⊆
      (univ : Finset (C.Dart×I)).image (fun d => dartEdge C d.1 d.2) := by
  classical
  have cross (a : V) (z : C.edgeSet×I) (ha : a∈(z.1:Sym2 V)) :
      s(Sum.inl a,Sum.inr z) ∈
        (univ : Finset (C.Dart×I)).image (fun d => dartEdge C d.1 d.2) := by
    obtain ⟨d,hda,hde⟩ := exists_dart_at_endpoint C z.1 a ha
    have he : (⟨d.edge,d.edge_mem⟩ : C.edgeSet)=z.1 := Subtype.ext hde
    apply mem_image.mpr
    refine ⟨(d,z.2),mem_univ _,?_⟩
    simp only [dartEdge,hda,he]
  intro e he
  rcases e with ⟨a,b⟩
  have hab := (mem_edgeSet _).mp (mem_edgeFinset.mp he)
  cases a with
  | inl a =>
    cases b with
    | inl b => exact False.elim hab
    | inr z => exact cross a z hab
  | inr z =>
    cases b with
    | inl b => simpa only [Sym2.eq_swap] using cross b z hab
    | inr z' => exact False.elim hab

/-- An explicit finite edge encoding supplies the certificate's weight budget. -/
theorem edge_count_le : (graph (I:=I) C).edgeFinset.card ≤
    2*C.edgeFinset.card*Fintype.card I := by
  classical
  have h := (card_le_card (edgeFinset_subset_dart_image (I:=I) C)).trans card_image_le
  simpa only [card_univ,Fintype.card_prod,C.dart_card_eq_twice_card_edges] using h

theorem unit_weight_bound (w : Sym2 (Vertex (I:=I) C) → ℝ)
    (hw : ∀ e∈(graph (I:=I) C).edgeSet,w e=1) :
    totalWeight (graph (I:=I) C) w≤2*C.edgeFinset.card*Fintype.card I := by
  rw [totalWeight_eq_card_mul _ _ 1 hw,mul_one]
  exact_mod_cast edge_count_le (I:=I) C
end LightEFTSpanners.ParallelSubdivision
