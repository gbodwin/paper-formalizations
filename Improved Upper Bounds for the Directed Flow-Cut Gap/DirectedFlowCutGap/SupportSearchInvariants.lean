import DirectedFlowCutGap.SupportSearchData

/-! Validity and cardinality are retained along every forward-updated prefix. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic

theorem visit_valid (adjacency : List Bits) (es : List (Bits×Bits)) (u : Bits) (xs : List Code)
    (N : ℕ) (hu : value u<N) (hx : ∀ x∈xs,value x.1<N) :
    ∀ x∈visit adjacency es u xs,value x.1<N := by
  unfold visit
  cases lookup u xs with
  | some x => exact hx
  | none =>
    cases predecessor adjacency es u xs with
    | none => exact hx
    | some x =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact hu
      · exact hx y hy

theorem pass_valid (adjacency : List Bits) (es : List (Bits×Bits)) (vs : List Bits) (xs : List Code)
    (N : ℕ) (hv : ∀ u∈vs,value u<N) (hx : ∀ x∈xs,value x.1<N) :
    ∀ x∈pass adjacency es vs xs,value x.1<N := by
  induction vs generalizing xs with
  | nil => exact hx
  | cons u us ih =>
    exact ih (visit adjacency es u xs) (fun v h => hv v (by simp [h])) (visit_valid adjacency es u xs N (hv u (by simp)) hx)

theorem rounds_valid (vs : List Bits) (adjacency : List Bits) (es : List (Bits×Bits)) (target : Bits)
    (fuel : List Bits) (N : ℕ) (hv : ∀ u∈vs,value u<N) (ht : value target<N) :
    ∀ x∈rounds vs adjacency es target fuel,value x.1<N := by
  induction fuel with
  | nil =>
    intro x hx
    simp only [rounds,List.mem_singleton] at hx
    subst x
    exact ht
  | cons u us ih => exact pass_valid adjacency es vs _ N hv ih

theorem visit_length (adjacency : List Bits) (es : List (Bits×Bits)) (u : Bits) (xs : List Code) :
    (visit adjacency es u xs).length≤xs.length+1 := by
  unfold visit
  cases lookup u xs with
  | some x => simp
  | none => cases predecessor adjacency es u xs <;> simp

theorem pass_length (adjacency : List Bits) (es : List (Bits×Bits)) (vs : List Bits) (xs : List Code) :
    (pass adjacency es vs xs).length≤xs.length+vs.length := by
  induction vs generalizing xs with
  | nil => simp [pass]
  | cons u us ih =>
    have h := ih (visit adjacency es u xs)
    have g := visit_length adjacency es u xs
    simp only [pass,List.length_cons]
    omega

theorem rounds_length (vs : List Bits) (adjacency : List Bits) (es : List (Bits×Bits)) (target : Bits) (fuel : List Bits) :
    (rounds vs adjacency es target fuel).length≤1+fuel.length*vs.length := by
  induction fuel with
  | nil => simp [rounds]
  | cons u us ih =>
    have h := pass_length adjacency es vs (rounds vs adjacency es target us)
    simp only [rounds,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end DirectedFlowCutGap.SupportRecoveryProgram
