import LengthExpander.NonnegativeCutSequence
import LengthExpander.IntegralDispersion

/-! An actual integral witness for the rescaled union of nonnegative cuts,
with all repaired copy/incidence/integrality constants made explicit. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def unionCut (Cs : List (EdgeLength V)) (s : ℕ) : EdgeLength V :=
  fun e => (1+1/((s:ℝ)-1))*totalCut Cs e

theorem exists_union_witness (G : SimpleGraph V) (A : NodeWeight V)
    (w : EdgeLength V) (h : ℝ) (s : ℕ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s) :
    ∃ D : Demand V, CutWitness G w (unionCut Cs s) A (2*h) (((s:ℝ)-1)/2) D ∧
      sequenceVolume G A h s w Cs ≤ 8*(densityBudget (2*weightSize A) s+1)*demandSize D := by
  classical
  obtain ⟨Ds,hr,hsize,geo⟩ := nonnegativeCut_witness_geometry G A w h s Cs hCs hh
  let a i := demandAllocation (hr i)
  have hpg := geo.parallelGreedy a hh (by omega)
  obtain ⟨D,hD,hshort,hm⟩ := exists_integral_dispersion hpg hs
  have hedge : Fintype.card (familyGraph a).edgeSet = sequenceVolume G A h s w Cs := by
    rw [familyGraph_edge_card a (geo.supportDisjoint hh (by omega)),sequenceVolume_eq_sum]
    exact sum_congr rfl (fun i _ => hsize i)
  refine ⟨D,⟨hD,?_,?_⟩,?_⟩
  · intro u v huv
    obtain ⟨x,y,hx,hy,hxy⟩ := hshort u v huv
    have hn := geo.short_pair_near a hh hxy
    simpa only [sequenceWeight_zero,hx,hy] using hn
  · intro u v huv
    obtain ⟨x,y,hx,hy,hxy⟩ := hshort u v huv
    have hf := geo.short_pair_far a hh hxy
    rw [sequenceWeight_eq_prefix,List.take_length] at hf
    have hprod : (2*h)*(((s:ℝ)-1)/2) = h*((s:ℝ)-1) := by ring
    change Far G (applyCut w (unionCut Cs s) ((2*h)*(((s:ℝ)-1)/2)))
      ((2*h)*(((s:ℝ)-1)/2)) u v
    rw [hprod]
    unfold unionCut
    rw [rescaled_cut_identity w (totalCut Cs) (by exact_mod_cast (show 1 < s by omega))]
    simpa only [hx,hy] using hf
  · rwa [hedge] at hm

end LengthExpander
