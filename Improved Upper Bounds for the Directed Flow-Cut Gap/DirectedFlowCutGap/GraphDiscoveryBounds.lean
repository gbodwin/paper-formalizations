import DirectedFlowCutGap.GraphDiscoveryWidths
import DirectedFlowCutGap.GraphLookupCalls

/-! Input-derived bounds for actual table passes and stable lookup. All field
bounds refer to the represented words; no unit-cost arithmetic is substituted. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension

def passBudget (m M W N S : ℕ) : ℕ :=
  m*(32*W+GraphRelaxationProgram.instructionBound M W N S+60)+3

theorem at_bound (adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (old : List Entry) (W N M : ℕ) (hW : 1 ≤ W) (hr : ∀ q∈rows,StoredBounded q W)
    (hi : value u<rows.length) (hu : u.length ≤ W) (ht : target.length ≤ W)
    (iu : value u ≤ N) (hx : ∀ x∈old,GraphRelaxationProgram.EntryBound W N x)
    (hm : old.length ≤ M) :
    atSteps adjacency rows sw target u old ≤ 32*W+GraphRelaxationProgram.instructionBound M W N sw.length+40 := by
  have hcmp := BinaryComparisonProgram.steps_bound u target
  have hscan := GraphRelaxationProgram.steps_bound adjacency rows sw u old W N hW hr hi hu iu hx
  have mono : GraphRelaxationProgram.instructionBound old.length W N sw.length ≤
      GraphRelaxationProgram.instructionBound M W N sw.length := by
    unfold GraphRelaxationProgram.instructionBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) _
  unfold atSteps
  split_ifs <;> omega

theorem pass_bound (adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (old : List Entry) (vertices : List Bits) (W N M : ℕ) (hW : 1 ≤ W)
    (hr : ∀ q∈rows,StoredBounded q W) (ht : target.length ≤ W)
    (hi : ∀ u∈vertices,value u<rows.length)
    (hv : ∀ u∈vertices,u.length ≤ W ∧ value u ≤ N)
    (hx : ∀ x∈old,GraphRelaxationProgram.EntryBound W N x) (hm : old.length ≤ M) :
    passSteps adjacency rows sw target old vertices ≤ passBudget vertices.length M W N sw.length := by
  induction vertices with
  | nil => simp [passSteps,passBudget]
  | cons u us ih =>
    have hu := hv u (by simp)
    have ha := at_bound adjacency rows sw target u old W N M hW hr (hi u (by simp)) hu.1 ht hu.2 hx hm
    have hh := ih (fun v hv => hi v (by simp [hv])) (fun v hv' => hv v (by simp [hv']))
    simp only [passSteps,passBudget,List.length_cons,Nat.add_mul] at *
    cases atVertex adjacency rows sw target u old <;> simp only at * <;> omega

theorem lookup_witness {u : Bits} {xs : List Entry} {q : Walk} (h : lookup u xs=some q) :
    ∃ x∈xs,x.2=q := by
  induction xs generalizing q with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    simp only [lookup] at h
    split at h
    · cases ht : lookup u xs with
      | none =>
        simp only [ht,GraphRelaxationProgram.pick,Option.some.injEq] at h
        exact ⟨x,List.mem_cons_self,h⟩
      | some y =>
        simp only [ht,GraphRelaxationProgram.pick,Option.some.injEq,GraphRelaxationProgram.choose] at h
        split at h
        · exact ⟨x,List.mem_cons_self,h⟩
        · obtain ⟨z,hz,hzq⟩ := ih ht
          exact ⟨z,List.mem_cons_of_mem _ hz,hzq.trans h⟩
    · obtain ⟨z,hz,hzq⟩ := ih h
      exact ⟨z,List.mem_cons_of_mem _ hz,hzq⟩

def lookupBudget (m W : ℕ) : ℕ := m*(32*W+400*(4*W+1)^2+60)+3

theorem lookup_finish_bound {x : Walk} {tail : Option Walk} {W : ℕ}
    (hx : StoredBounded x.cost W) (ht : ∀ y,tail=some y → StoredBounded y.cost W) :
    lookupFinishSteps x tail ≤ 400*(4*W+1)^2+13 := by
  cases tail with
  | none => simp [lookupFinishSteps]
  | some y =>
    have hy := ht y rfl
    have hc := RationalComparisonProgram.instructions_bound x.cost y.cost
    have sz : RationalComparisonProgram.inputSize x.cost y.cost ≤ 4*W+1 := by
      rcases hx with ⟨hxn,hxd⟩;rcases hy with ⟨hyn,hyd⟩
      dsimp [RationalComparisonProgram.inputSize];omega
    have hh := hc.trans (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left sz 2))
    simp only [lookupFinishSteps,GraphRelaxationProgram.pickSteps]
    omega

theorem lookup_bound (u : Bits) (xs : List Entry) (W : ℕ)
    (hu : u.length ≤ W) (hx : ∀ x∈xs,x.1.length ≤ W ∧ StoredBounded x.2.cost W) :
    lookupSteps u xs ≤ lookupBudget xs.length W := by
  induction xs with
  | nil => simp [lookupSteps,lookupBudget]
  | cons x xs ih =>
    have hhead := hx x (by simp)
    have htail : ∀ y∈xs,y.1.length ≤ W ∧ StoredBounded y.2.cost W := fun y hy => hx y (by simp [hy])
    have hc := BinaryComparisonProgram.steps_bound x.1 u
    have hf := lookup_finish_bound (tail:=lookup u xs) hhead.2 (fun y hy => by
      obtain ⟨z,hz,rfl⟩ := lookup_witness hy
      exact (htail z hz).2)
    have hh := ih htail
    simp only [lookupSteps,lookupBudget,List.length_cons,Nat.add_mul] at *
    split_ifs <;> omega

end DirectedFlowCutGap.GraphDiscoveryProgram
