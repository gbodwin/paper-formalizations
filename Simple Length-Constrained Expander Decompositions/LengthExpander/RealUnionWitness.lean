import LengthExpander.RealCutSequence
import LengthExpander.IntegralDispersion

/-! An all-real union witness. Only the auxiliary graph counting threshold
is rounded; the strict final h(s-1) geometry retains the original real s. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def realUnionCut (Cs : List (EdgeLength V)) (s : ℝ) : EdgeLength V :=
  fun e => (1+1/(s-1))*totalCut Cs e

theorem exists_real_union_witness (G : SimpleGraph V) (A : NodeWeight V)
    (w : EdgeLength V) (h s : ℝ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s) :
    ∃ D : Demand V, CutWitness G w (realUnionCut Cs s) A (2*h) ((s-1)/2) D ∧
      sequenceVolume G A h s w Cs ≤ 8*(densityBudget (2*weightSize A) ⌊s⌋₊+1)*demandSize D := by
  classical
  obtain ⟨Ds,hr,hsize,geo⟩ := real_nonnegativeCut_geometry G A w h s Cs hCs hh (by linarith)
  let a i := demandAllocation (hr i)
  have hfloor := (floor_threshold_bounds hs).1
  have gi := geo.toFloor hh (by linarith : 0 ≤ s)
  have hpg := gi.parallelGreedy a hh (by omega)
  obtain ⟨D,hD,hshort,hm⟩ := exists_integral_dispersion hpg hfloor
  have hedge : Fintype.card (familyGraph a).edgeSet = sequenceVolume G A h s w Cs := by
    rw [familyGraph_edge_card a (gi.supportDisjoint hh (by omega)),sequenceVolume_eq_sum]
    exact sum_congr rfl (fun i _ => hsize i)
  refine ⟨D,⟨hD,?_,?_⟩,?_⟩
  · intro u v huv
    obtain ⟨x,y,hx,hy,hxy⟩ := hshort u v huv
    have hn := gi.short_pair_near a hh hxy
    simpa only [sequenceWeight_zero,hx,hy] using hn
  · intro u v huv
    obtain ⟨x,y,hx,hy,hxy⟩ := hshort u v huv
    have hf := geo.short_pair_far a hh hxy
    rw [sequenceWeight_eq_prefix,List.take_length] at hf
    have hprod : (2*h)*((s-1)/2) = h*(s-1) := by ring
    change Far G (applyCut w (realUnionCut Cs s) ((2*h)*((s-1)/2)))
      ((2*h)*((s-1)/2)) u v
    rw [hprod]
    unfold realUnionCut
    rw [rescaled_cut_identity w (totalCut Cs) (by linarith : 1 < s)]
    simpa only [hx,hy] using hf
  · rwa [hedge] at hm

end LengthExpander
