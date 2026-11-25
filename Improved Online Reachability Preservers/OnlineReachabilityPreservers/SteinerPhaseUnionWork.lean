import OnlineReachabilityPreservers.SteinerIntervalWork

/-! Meter the union of the two phase graphs while keeping their exact arc set. -/

namespace OnlineReachabilityPreservers

open Finset

private def appendRowsWithWordWork {A : Type*} (right : List A) : List A → List A × ℕ
  | [] => (right, 2)
  | head :: tail =>
    let rest := appendRowsWithWordWork right tail
    (head :: rest.1, rest.2 + 5)

private theorem appendRowsWithWordWork_spec {A : Type*} (right left : List A) :
    appendRowsWithWordWork right left = (left ++ right, 5 * left.length + 2) := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
    simp only [appendRowsWithWordWork, ih, List.cons_append, List.length_cons, Nat.mul_succ]

private def appendMultisetsWithWordWork {A : Type*} (left right : Multiset A) : Multiset A × ℕ :=
  Quotient.liftOn₂ left right
    (fun l r => let out := appendRowsWithWordWork r l; ((out.1 : Multiset A), out.2))
    (by
      intro a b c d leftPerm rightPerm
      simp only [appendRowsWithWordWork_spec, leftPerm.length_eq]
      exact congrArg (fun rows => (rows, 5 * c.length + 2)) (Quotient.sound (leftPerm.append rightPerm)))

private theorem appendMultisetsWithWordWork_spec {A : Type*} (left right : Multiset A) :
    appendMultisetsWithWordWork left right = (left + right, 5 * left.card + 2) := by
  refine Quotient.inductionOn₂ left right ?_
  intro a b
  change (let out := appendRowsWithWordWork b a; ((out.1 : Multiset A), out.2)) = _
  rw [appendRowsWithWordWork_spec]
  rfl

private def missingFromWithWordWork {A : Type*} [DecidableEq A] (left : Finset A) (key : A) : Bool × ℕ :=
  let found := memFinsetWithWordWork key left
  (!found.1, found.2 + 3)

private theorem missingFromWithWordWork_spec {A : Type*} [DecidableEq A] (left : Finset A) (key : A) :
    let out := missingFromWithWordWork left key
    out.1 = decide (key ∉ left) ∧ out.2 ≤ 12 * left.card + 9 := by
  let found := memFinsetWithWordWork key left
  obtain ⟨present, spent⟩ := memFinsetWithWordWork_spec key left
  change (!found.1) = _ ∧ found.2 + 3 ≤ _
  exact ⟨by rw [present, decide_not], Nat.add_le_add_right spent 3⟩

private theorem unionRemainderWithWordWork_disjoint {A : Type*} [DecidableEq A] (left right : Finset A) :
    Disjoint left (filterFinsetWithWordWork (missingFromWithWordWork left) right).1 := by
  rw [(filterFinsetWithWordWork_spec _ _).1]
  apply disjoint_left.mpr
  intro key contained added
  have fresh := (mem_filter.mp added).2
  rw [(missingFromWithWordWork_spec left key).1, decide_eq_true_eq] at fresh
  exact fresh contained

/-- Scan the second graph for arcs absent from the first, then append the
two disjoint lists. The count includes both membership scans and the append. -/
def unionFinsetWithWordWork {A : Type*} [DecidableEq A] (left right : Finset A) : Finset A × ℕ :=
  let fresh := filterFinsetWithWordWork (missingFromWithWordWork left) right
  let combined := appendMultisetsWithWordWork left.val fresh.1.val
  have disjoint := unionRemainderWithWordWork_disjoint left right
  have nodes : combined.1.Nodup :=
    (congrArg Prod.fst (appendMultisetsWithWordWork_spec left.val fresh.1.val)).symm ▸
      (left.disjUnion fresh.1 disjoint).nodup
  (⟨combined.1, nodes⟩, fresh.2 + combined.2 + 6)

theorem unionFinsetWithWordWork_spec {A : Type*} [DecidableEq A] (left right : Finset A) :
    let result := unionFinsetWithWordWork left right
    result.1 = left ∪ right ∧
      result.2 ≤ right.card * (12 * left.card + 19) + 5 * left.card + 10 := by
  let fresh := filterFinsetWithWordWork (missingFromWithWordWork left) right
  have disjoint := unionRemainderWithWordWork_disjoint left right
  obtain ⟨selected, count⟩ := filterFinsetWithWordWork_spec (missingFromWithWordWork left) right
  have remains : fresh.1 = right \ left := by
    change fresh.1 = _ at selected
    rw [selected]
    ext key
    simp only [mem_filter, mem_sdiff, (missingFromWithWordWork_spec left key).1, decide_eq_true_eq]
  have append := appendMultisetsWithWordWork_spec left.val fresh.1.val
  refine ⟨?_, ?_⟩
  · calc
      _ = left.disjUnion fresh.1 disjoint := eq_of_veq (congrArg Prod.fst append)
      _ = left ∪ fresh.1 := disjUnion_eq_union _ _ _
      _ = left ∪ right := by rw [remains, union_sdiff_self_eq_union]
  · have cost : fresh.2 ≤ right.card * (12 * left.card + 19) + 2 :=
      count (12 * left.card + 9) (fun key _ => (missingFromWithWordWork_spec left key).2)
    change fresh.2 + (appendMultisetsWithWordWork left.val fresh.1.val).2 + 6 ≤ _
    rw [append]
    change fresh.2 + (5 * left.card + 2) + 6 ≤ _
    omega

/-- A uniform per-prefix allowance for the union of two arc sets. -/
def steinerPhaseUnionWordBudget (n : ℕ) : ℕ :=
  n^2 * (12 * n^2 + 19) + 5 * n^2 + 10

theorem steinerPhaseUnionWordBudget_bound {V : Type*} [DecidableEq V] [Fintype V]
    (left right : Arcs V) : (unionFinsetWithWordWork left right).2 ≤ steinerPhaseUnionWordBudget (Fintype.card V) := by
  have cardinal (H : Arcs V) : H.card ≤ (Fintype.card V)^2 := by
    simpa only [Fintype.card_prod, pow_two] using card_le_univ H
  refine (unionFinsetWithWordWork_spec left right).2.trans ?_
  unfold steinerPhaseUnionWordBudget
  gcongr <;> exact cardinal _

end OnlineReachabilityPreservers
