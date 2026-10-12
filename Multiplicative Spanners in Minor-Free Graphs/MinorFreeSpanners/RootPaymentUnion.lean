import MinorFreeSpanners.BranchingPhaseConservation

/-! Join the global high-degree bill and the actual individual weak-root bills.
The weak heavy-edge union is paid once even when two weak roots touch an edge;
every retained root credit and every supplied old-credit allocation is counted
exactly once. This is the finite accounting used by the earlier root phases. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable
variable {J E : Type*} [Fintype J]

 theorem root_payment_union (high : Finset J) (heavy : J → Finset E)
    (w : E → ℝ) (keep used bridge : J → ℝ) (highBill c : ℝ)
    (hw : ∀ j,j∉high → ∀ e∈heavy j,0≤w e)
    (hhigh : highBill+(∑ j∈high,keep j)≤(∑ j∈high,used j)+c*(∑ j∈high,bridge j))
    (hweak : ∀ j,j∉high → (∑ e∈heavy j,w e)+keep j≤used j+c*bridge j) :
    highBill+(∑ e∈(Finset.univ\high).biUnion heavy,w e)+(∑ j,keep j)≤
      (∑ j,used j)+c*(∑ j,bridge j) := by
  classical
  have hl := Finset.sum_le_sum (s:=Finset.univ\high)
    (fun j hj => hweak j (Finset.mem_sdiff.mp hj).2)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum] at hl
  have hu := finite_union_weight_le (Finset.univ\high) heavy w
    (fun j hj => hw j (Finset.mem_sdiff.mp hj).2)
  have hk := Finset.sum_sdiff (f:=keep) (Finset.subset_univ high)
  have hc := Finset.sum_sdiff (f:=used) (Finset.subset_univ high)
  have hb := Finset.sum_sdiff (f:=bridge) (Finset.subset_univ high)
  have hb' := congrArg (fun x : ℝ => c*x) hb
  rw [mul_add] at hb'
  linarith

end MinorFreeSpanners
