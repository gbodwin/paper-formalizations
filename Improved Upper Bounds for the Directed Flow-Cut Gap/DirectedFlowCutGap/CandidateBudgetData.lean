import DirectedFlowCutGap.CandidatePhysicalCut

/-!
# Computing the closure budget from the current mask

Each unremoved core vertex contributes one unit for each sign and
positive threshold level. Ports, removed vertices, and level zero
contribute zero.
-/

namespace DirectedFlowCutGap.CandidateBudgetData

open scoped BigOperators
open BinaryArithmetic CandidateGridOptimizer CandidateThresholdClosure
open EncodedCandidateCapacity MinimumClosureCut

def remaining (flags : Bits) : ℕ := (flags.filter (fun b => !b)).length

@[simp] theorem remaining_cons (b : Bool) (flags : Bits) :
    remaining (b::flags)=remaining flags+(if b then 0 else 1) := by
  cases b <;> simp [remaining]

theorem remaining_le (flags : Bits) : remaining flags≤flags.length := List.length_filter_le _ _

private theorem remaining_sum (flags : Bits) :
    remaining flags=(flags.map (fun b => if b then 0 else 1)).sum := by
  induction flags with
  | nil => rfl
  | cons b bs ih => simp [ih,Nat.add_comm]

theorem remaining_vector {n : ℕ} (flags : Vector Bool n) :
    remaining flags.toList=(∑ i : Fin n, if flags[i.val] then 0 else 1) := by
  have words : flags.toList=List.ofFn (fun i : Fin n => flags[i.val]) := by
    rw [← Vector.toList_ofFn,Vector.ofFn_getElem]
  rw [remaining_sum,words,List.map_ofFn,List.sum_ofFn]
  rfl

theorem budget_exact {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ) :
    budget (CandidatePhysicalCut.problem D s t L B)=2*L*remaining D.removed.toList := by
  have levels (p : Point (Fin n)) :
      (∑ i : Fin (L+1), (D.nodeCost (p,i)).natAbs)=L*(D.cost p).natAbs := by
    rw [Fin.sum_univ_succ]
    simp [Input.nodeCost,Finset.sum_const]
  have costs : (∑ p : Point (Fin n),(D.cost p).natAbs)=2*remaining D.removed.toList := by
    rw [remaining_vector,Finset.mul_sum]
    unfold Point TerminalPorts.Vertex
    rw [Fintype.sum_prod_type,Fintype.sum_sum_type]
    simp only [Fintype.sum_bool,Input.cost,Int.natAbs_zero,add_zero,Finset.sum_const_zero]
    apply Finset.sum_congr rfl
    intro i _
    cases D.removed[i.val] <;> simp
  calc
    budget (CandidatePhysicalCut.problem D s t L B) =
        ∑ a : Node (Point (Fin n)) L,(D.nodeCost a).natAbs := by
      unfold budget
      apply Finset.sum_congr rfl
      intro a _
      rw [D.nodeCost_eq s t L B]
    _ = ∑ p : Point (Fin n), ∑ i : Fin (L+1),(D.nodeCost (p,i)).natAbs := by
      apply Fintype.sum_prod_type
    _ = L*(∑ p : Point (Fin n),(D.cost p).natAbs) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => levels p)
    _ = _ := by rw [costs]; ring

end DirectedFlowCutGap.CandidateBudgetData
