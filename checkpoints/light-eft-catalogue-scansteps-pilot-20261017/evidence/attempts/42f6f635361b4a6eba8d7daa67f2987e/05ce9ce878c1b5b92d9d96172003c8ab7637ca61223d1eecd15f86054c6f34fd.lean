import LightEFTSpanners.NativeEulerianSplit
import LightEFTSpanners.NativeEulerianCuts

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The cut separating all terminals from the center counts exactly its
original nonloop incident identities. Center loops contribute zero. -/
theorem center_cut_card (G : Graph (Option V) E) :
    cutSize G (liftSet (univ:Finset V))=Fintype.card (CenterInc G) := by
  rw [cutSize_center_decomposition]
  have hz : cutSize (centerCore G) (univ:Finset V)=0 := by
    simp [cutSize_sum,Graph.edgeCut]
  rw [hz,zero_add]
  simp [mass]

/-- The literal native split removes exactly two nonloop center incidences.
This provides a well-founded progress measure for complete center elimination. -/
theorem centerSplit_card_decrease (G : Graph (Option V) E)
    (i j : CenterInc G) (hij : i≠j) :
    Fintype.card (CenterInc (centerSplit G i j))+2=Fintype.card (CenterInc G) := by
  have h := centerSplit_cutSize G i j hij (univ:Finset V)
  simp only [mem_univ,and_self,ite_true,center_cut_card] at h
  exact_mod_cast h.symm

/-- Genuine even-degree multigraph splitting with explicit native output and
strict progress. Every chosen nonloop center edge obtains a distinct partner;
all specified 2k-edge-fault connections and every vertex are preserved. The
output again has even actual degrees, with exactly two fewer center incidences.
This uniform-threshold case is the splitting dependency used for Steiner forests. -/
theorem exists_native_eulerian_step (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ) (hconn : RequiredConnectivity G P k)
    (hdeg : ∀ v,Even (nativeDegree G v)) (i : CenterInc G) :
    ∃ j : CenterInc G,j≠i ∧
      RequiredConnectivity (centerSplit G i j) P k ∧
      (∀ v,Even (nativeDegree (centerSplit G i j) v)) ∧
      (centerSplit G i j).vertexSet=G.vertexSet ∧
      Fintype.card (CenterInc (centerSplit G i j))+2=Fintype.card (CenterInc G) := by
  have he : EvenCuts G := even_cut_of_even_degrees G hdeg
  have hp : 0<Fintype.card (CenterInc G) := Fintype.card_pos_iff.mpr ⟨i⟩
  have hc : Even (Fintype.card (CenterInc G):ℤ) := by
    rw [←center_cut_card G]
    exact he _
  have hdegree : 2≤Fintype.card (CenterInc G) := by
    obtain ⟨z,hz⟩ := hc
    omega
  obtain ⟨j,hji,hconn',he'⟩ := exists_eulerian_required_split G P k hconn he hdegree i
  exact ⟨j,hji,hconn',even_degrees_of_even_cuts _ he',rfl,
    centerSplit_card_decrease G i j (Ne.symm hji)⟩
end LightEFTSpanners.EvenSplitting
