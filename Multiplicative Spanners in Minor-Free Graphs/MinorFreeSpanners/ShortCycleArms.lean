import MinorFreeSpanners.ShortCycleWalks
import MinorFreeSpanners.CoarsePathDetourGap
import MinorFreeSpanners.BoundedSurplusPayment

/-! The three consecutive light pieces of a short-cycle cluster are actual
subpaths of one simple path. Their shared endpoints are counted exactly once. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

structure ShortCycleArms {I : Type*} (H : SimpleGraph I) (d : I → ℝ)
    (L D : ℝ) (x y : I) where
  leftEnd : I
  rightEnd : I
  left : H.Walk x leftEnd
  middle : H.Walk x y
  right : H.Walk y rightEnd
  whole_path : (left.reverse.append (middle.append right)).IsPath
  left_lower : L≤pathMass (fun i => d i+1) left
  right_lower : L≤pathMass (fun i => d i+1) right
  left_upper : pathMass (fun i => d i+1) left<L+D+1
  right_upper : pathMass (fun i => d i+1) right<L+D+1
  middle_upper : pathMass (fun i => d i+1) middle≤2*(L+D+1)

namespace ShortCycleArms
variable {I : Type*} {H : SimpleGraph I} {d : I → ℝ} {L D : ℝ} {x y : I}

noncomputable def carrier (S : ShortCycleArms H d L D x y) : Finset I := by
  classical
  exact (S.left.reverse.append (S.middle.append S.right)).support.toFinset

 theorem left_path (S : ShortCycleArms H d L D x y) : S.left.IsPath := by
  simpa using S.whole_path.of_append_left.reverse

 theorem middle_path (S : ShortCycleArms H d L D x y) : S.middle.IsPath :=
  S.whole_path.of_append_right.of_append_left

 theorem right_path (S : ShortCycleArms H d L D x y) : S.right.IsPath :=
  S.whole_path.of_append_right.of_append_right

 theorem carrier_eq (S : ShortCycleArms H d L D x y) :
    S.carrier=S.left.support.toFinset∪S.middle.support.toFinset∪S.right.support.toFinset := by
  classical
  ext i
  simp only [carrier,List.mem_toFinset,Walk.mem_support_append_iff,
    Walk.support_reverse,List.mem_reverse,Finset.mem_union]
  tauto

 theorem connected (S : ShortCycleArms H d L D x y) : ConnectedWithin H S.carrier :=
  forest_walk_support_connected _

 theorem nonempty (S : ShortCycleArms H d L D x y) : S.carrier.Nonempty := by
  classical
  exact ⟨S.leftEnd,List.mem_toFinset.mpr (S.left.reverse.append (S.middle.append S.right)).start_mem_support⟩

 theorem mass_exact (S : ShortCycleArms H d L D x y) :
    (∑ i∈S.carrier,(d i+1))+(d x+1)+(d y+1)=
      pathMass (fun i => d i+1) S.left+pathMass (fun i => d i+1) S.middle+
        pathMass (fun i => d i+1) S.right := by
  classical
  have h1 := pathMass_append (fun i => d i+1) S.left.reverse (S.middle.append S.right) S.whole_path
  have h2 := pathMass_append (fun i => d i+1) S.middle S.right S.whole_path.of_append_right
  rw [pathMass_reverse] at h1
  change (∑ i∈S.carrier,(d i+1))+(d x+1)=_ at h1
  linarith

 theorem credit_gap [Fintype I] (S : ShortCycleArms H d L D x y)
    (credit : I → ℝ) (c e g ell : ℝ) (hc : 0≤c) (hg : 2≤g)
    (hdx : d x≤D) (hdy : d y≤D) (he : ell≤e)
    (hgap : (g-1)*e+1≤pathMass (fun i => d i+1) S.middle)
    (hcredit : ∀ i∈S.carrier,c*d i≤credit i) :
    c*(2*(L+2*D+1)+e)+c*((g-2)*ell-6*D-4)≤
      (∑ i∈S.carrier,credit i)+c*(internalEdges H S.carrier).card := by
  classical
  have hsum : c*(∑ i∈S.carrier,d i)≤∑ i∈S.carrier,credit i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hcredit i hi
  have hedge := internalEdges_card_lower H S.carrier S.connected S.nonempty
  have hcard : (S.carrier.card:ℝ)≤(internalEdges H S.carrier).card+1 := by
    exact_mod_cast (show S.carrier.card≤(internalEdges H S.carrier).card+1 by omega)
  have hcardc := mul_le_mul_of_nonneg_left hcard hc
  have hmass := S.mass_exact
  have hl := S.left_lower
  have hr := S.right_lower
  have hm : 2*L+(g-1)*e-2*D-1≤∑ i∈S.carrier,(d i+1) := by linarith
  have hmc := mul_le_mul_of_nonneg_left hm hc
  have hmadd : (∑ i∈S.carrier,(d i+1))=(∑ i∈S.carrier,d i)+S.carrier.card := by
    simp [Finset.sum_add_distrib]
  rw [hmadd] at hmc
  have hec := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left he (show 0≤g-2 by linarith)) hc
  nlinarith

end ShortCycleArms
end MinorFreeSpanners
