import LengthExpander.Demands
import LengthExpander.PairingLists
import Mathlib.Data.Finset.Dedup

/-! Count oriented pairs in finite lists as actual integral demands. -/
namespace LengthExpander
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def listDemand : List (V × V) → Demand V
  | [] => fun _ _ => 0
  | (x,y)::L => fun u v => (if u = x ∧ v = y then 1 else 0) + listDemand L u v

@[simp] theorem listDemand_nil : listDemand ([] : List (V × V)) = fun _ _ => 0 := rfl

@[simp] theorem listDemand_cons (x y : V) (L : List (V × V)) (u v : V) :
    listDemand ((x,y)::L) u v = (if u = x ∧ v = y then 1 else 0) + listDemand L u v := rfl

theorem listDemand_size (L : List (V × V)) : demandSize (listDemand L) = L.length := by
  classical
  induction L with
  | nil => simp [demandSize]
  | cons e L ih =>
    rcases e with ⟨x,y⟩
    have hd (u : V) : (∑ v : V, if u = x ∧ v = y then 1 else 0) = if u = x then 1 else 0 := by
      by_cases h : u = x <;> simp [h]
    simp only [demandSize,listDemand_cons,sum_add_distrib]
    simp_rw [hd]
    have hx : (∑ u : V, if u = x then 1 else 0) = 1 := by simp
    rw [hx]
    change 1 + demandSize (listDemand L) = L.length + 1
    omega

theorem listDemand_positive_iff (L : List (V × V)) (u v : V) :
    0 < listDemand L u v ↔ (u,v) ∈ L := by
  classical
  induction L with
  | nil => simp
  | cons e L ih =>
    rcases e with ⟨x,y⟩
    simp only [listDemand_cons,List.mem_cons,Prod.mk.injEq]
    by_cases he : u = x ∧ v = y <;> simp [he,ih]

/-- Incoming plus outgoing demand is exactly the endpoint occurrence count. -/
theorem listDemand_incidence (L : List (V × V)) (u : V) :
    (∑ v, listDemand L u v) + (∑ v, listDemand L v u) =
      (pairEndpoints L).count u := by
  classical
  induction L with
  | nil => simp [pairEndpoints]
  | cons e L ih =>
    rcases e with ⟨x,y⟩
    simp only [listDemand_cons,sum_add_distrib,pairEndpoints,List.flatMap_cons,
      List.count_append,List.count_cons,List.count_nil]
    have hx : (∑ v : V, if u = x ∧ v = y then 1 else 0) = if u = x then 1 else 0 := by
      by_cases h : u = x <;> simp [h]
    have hy : (∑ v : V, if v = x ∧ u = y then 1 else 0) = if u = y then 1 else 0 := by
      by_cases h : u = y <;> simp [h]
    rw [hx,hy]
    change (if u = x then 1 else 0) + (∑ v, listDemand L u v) +
      ((if u = y then 1 else 0) + (∑ v, listDemand L v u)) = _
    simp only [beq_iff_eq]
    simp only [pairEndpoints] at ih
    simp only [eq_comm]
    omega

/-- Membership count for a finset list, stated without reliance on its order. -/
theorem count_finset_toList (S : Finset V) (u : V) :
    S.toList.count u = if u ∈ S then 1 else 0 := by
  classical
  by_cases hu : u ∈ S
  · simpa only [if_pos hu] using List.count_eq_one_of_mem S.nodup_toList (mem_toList.mpr hu)
  · rw [if_neg hu]
    exact List.count_eq_zero.mpr (by simpa using hu)

end LengthExpander
