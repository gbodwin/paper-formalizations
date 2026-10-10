import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Lean.Elab.Tactic.Omega

/-! Pair distinct children in their list order. An odd final child is paired
with its parent. The endpoint list contains every child exactly once and
at most one extra parent; this is the finite combinatorics of dispersion. -/
namespace LengthExpander
variable {V : Type*}

def pairChildren (p : V) : List V → List (V × V)
  | [] => []
  | [x] => [(x,p)]
  | x :: y :: L => (x,y) :: pairChildren p L

def pairEndpoints (L : List (V × V)) : List V := L.flatMap (fun e => [e.1,e.2])

@[simp] theorem pairEndpoints_length (L : List (V × V)) :
    (pairEndpoints L).length = 2*L.length := by
  induction L with
  | nil => simp [pairEndpoints]
  | cons e L ih => simp [pairEndpoints] at *; omega

/-- Pairing neither drops nor duplicates a child; the only possible extra
endpoint is one copy of the parent. -/
theorem pairChildren_endpoints (p : V) (L : List V) :
    pairEndpoints (pairChildren p L) = L ∨
      pairEndpoints (pairChildren p L) = L ++ [p] := by
  induction L using pairChildren.induct with
  | case1 => exact Or.inl rfl
  | case2 x => exact Or.inr rfl
  | case3 x y L ih =>
    rcases ih with ih | ih
    · exact Or.inl (by simpa [pairChildren,pairEndpoints] using congrArg (fun L => x::y::L) ih)
    · exact Or.inr (by simpa [pairChildren,pairEndpoints] using congrArg (fun L => x::y::L) ih)

theorem pairChildren_large (p : V) (L : List V) :
    L.length ≤ 2*(pairChildren p L).length := by
  rw [← pairEndpoints_length]
  rcases pairChildren_endpoints p L with h | h
  · rw [h]; exact Nat.le_refl _
  · rw [h,List.length_append]; simp

theorem pairChildren_nodup (p : V) {L : List V} (hL : L.Nodup) (hp : p ∉ L) :
    (pairEndpoints (pairChildren p L)).Nodup := by
  rcases pairChildren_endpoints p L with h | h
  · simpa only [h] using hL
  · rw [h]
    simpa using hL.concat hp

/-- Each child is used once, while the parent is used at most once. -/
theorem pairChildren_count [DecidableEq V] (p u : V) (L : List V) :
    (pairEndpoints (pairChildren p L)).count u ≤ L.count u + if u = p then 1 else 0 := by
  rcases pairChildren_endpoints p L with h | h
  · rw [h]; omega
  · rw [h,List.count_append]
    by_cases hup : u = p
    · subst u; simp
    · have hz : ([p] : List V).count u = 0 := List.count_eq_zero.mpr (by simpa using hup)
      simp [hup,hz]

/-- Every dispersed pair is two children, or a final child and its parent. -/
theorem pairChildren_mem (p : V) {L : List V} {x y : V}
    (hxy : (x,y) ∈ pairChildren p L) : x ∈ L ∧ (y ∈ L ∨ y = p) := by
  induction L using pairChildren.induct with
  | case1 => simp [pairChildren] at hxy
  | case2 z =>
    have hz : x = z ∧ y = p := by simpa [pairChildren] using hxy
    simp [hz]
  | case3 z t L ih =>
    simp only [pairChildren,List.mem_cons] at hxy
    rcases hxy with hxy | hxy
    · cases hxy
      simp
    · obtain ⟨hx,hy | hy⟩ := ih hxy
      · exact ⟨by simp [hx],Or.inl (by simp [hy])⟩
      · exact ⟨by simp [hx],Or.inr hy⟩

end LengthExpander
