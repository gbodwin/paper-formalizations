import GreedyShortcuts.DirectedPaths
import Mathlib.Data.List.OfFn

/-! Executable finite-horizon min-plus relaxation on materialized array rows.
The cap is a sentinel, not a claim that unreachable distance is zero. -/
namespace GreedyShortcuts.FiniteDistanceDP
open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking

/-- A finite minimum with an explicit fallback. -/
def minimum (fallback : ℕ) : List ℕ → ℕ
  | [] => fallback
  | x::xs => min x (minimum fallback xs)

theorem minimum_le_fallback (b : ℕ) (xs : List ℕ) : minimum b xs ≤ b := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact (Nat.min_le_right _ _).trans ih

theorem minimum_le_mem (b : ℕ) {xs : List ℕ} {x : ℕ} (hx : x∈xs) : minimum b xs ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.min_le_left _ _
    · exact (Nat.min_le_right _ _).trans (ih hx)

theorem minimum_attained (b : ℕ) (xs : List ℕ) : minimum b xs=b ∨ minimum b xs∈xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    by_cases h : x ≤ minimum b xs
    · exact Or.inr (by simp [minimum,Nat.min_eq_left h])
    · have he : minimum b (x::xs)=minimum b xs := Nat.min_eq_right (by omega)
      rw [he]
      exact ih.elim Or.inl (fun hx => Or.inr (List.mem_cons_of_mem x hx))

variable {n : ℕ}

/-- Row entries are materialized; the previous horizon is evaluated once. -/
def rows (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target : Fin n) : ℕ → Vector ℕ n
  | 0 => Vector.ofFn (fun u => if u=target then 0 else cap)
  | k+1 =>
    let previous := rows edge weight cap target k
    Vector.ofFn (fun u => minimum cap (previous[u] :: List.ofFn (fun v : Fin n =>
      if u≠v ∧ edge u v=true then weight u v+previous[v] else cap)))

def value (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target : Fin n) (k : ℕ) (u : Fin n) : ℕ :=
  (rows edge weight cap target k)[u]

@[simp] theorem value_zero (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target u : Fin n) : value edge weight cap target 0 u = if u=target then 0 else cap := by
  simp [value,rows]

theorem value_succ (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target u : Fin n) (k : ℕ) :
    value edge weight cap target (k+1) u = minimum cap
      (value edge weight cap target k u :: List.ofFn (fun v : Fin n =>
        if u≠v ∧ edge u v=true then weight u v+value edge weight cap target k v else cap)) := by
  simp [value,rows]

theorem value_le_cap (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target u : Fin n) (k : ℕ) : value edge weight cap target k u ≤ cap := by
  cases k with
  | zero => simp only [value_zero]; split_ifs <;> omega
  | succ k => rw [value_succ]; exact minimum_le_fallback _ _

theorem value_succ_le (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target u : Fin n) (k : ℕ) :
    value edge weight cap target (k+1) u ≤ value edge weight cap target k u := by
  rw [value_succ]
  exact minimum_le_mem _ (List.mem_cons_self ..)

theorem value_le_step (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target u v : Fin n) (k : ℕ) (hne : u≠v) (he : edge u v=true) :
    value edge weight cap target (k+1) u ≤ weight u v+value edge weight cap target k v := by
  rw [value_succ]
  apply minimum_le_mem
  apply List.mem_cons_of_mem
  apply List.mem_ofFn.mpr
  exact ⟨v,by simp [hne,he]⟩

/-- Actual edge-weight sum of the native directed walk. -/
def walkCost (weight : Fin n → Fin n → ℕ) {s t : Fin n} (p : DWalk s t) : ℕ :=
  (p.darts.map (fun d => weight d.fst d.snd)).sum

@[simp] theorem walkCost_nil (weight : Fin n → Fin n → ℕ) (s : Fin n) :
    walkCost weight (Walk.nil : DWalk s s)=0 := rfl

@[simp] theorem walkCost_cons (weight : Fin n → Fin n → ℕ) {s u t : Fin n}
    (h : (⊤ : SimpleGraph (Fin n)).Adj s u) (p : DWalk u t) :
    walkCost weight (.cons h p)=weight s u+walkCost weight p := by
  simp [walkCost,Walk.darts_cons]

/-- Every nonsentinel result is attained by a real allowed walk. -/
theorem value_sound (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target : Fin n) (k : ℕ) (u : Fin n)
    (hval : value edge weight cap target k u < cap) :
    ∃ p : DWalk u target, Allowed (fun a b => edge a b=true) p ∧
      p.length ≤ k ∧ walkCost weight p=value edge weight cap target k u := by
  induction k generalizing u with
  | zero =>
    by_cases hu : u=target
    · subst u
      exact ⟨.nil,allowed_nil _ _,by simp,by simp⟩
    · simp [hu] at hval
  | succ k ih =>
    rw [value_succ] at hval ⊢
    let xs := value edge weight cap target k u :: List.ofFn (fun v : Fin n =>
      if u≠v ∧ edge u v=true then weight u v+value edge weight cap target k v else cap)
    change minimum cap xs < cap at hval
    have hm : minimum cap xs∈xs := (minimum_attained cap xs).resolve_left (by omega)
    rcases List.mem_cons.mp hm with hold | hnew
    · obtain ⟨p,hp,hlen,hcost⟩ := ih u (by omega)
      exact ⟨p,hp,by omega,hcost.trans hold.symm⟩
    · obtain ⟨v,hv⟩ := List.mem_ofFn.mp hnew
      by_cases he : u≠v ∧ edge u v=true
      · simp only [ite_eq_left he] at hv
        obtain ⟨p,hp,hlen,hcost⟩ := ih v (by omega)
        let h : (⊤ : SimpleGraph (Fin n)).Adj u v := by simpa using he.1
        refine ⟨.cons h p,(allowed_cons _ h p).mpr ⟨he.2,hp⟩,by simp;omega,?_⟩
        rw [walkCost_cons,hcost,hv]
      · simp only [ite_eq_right he] at hv
        omega

/-- Every allowed walk within the horizon upper-bounds the computed value,
including walks whose weight is larger than the cap. -/
theorem value_le_walk (edge : Fin n → Fin n → Bool) (weight : Fin n → Fin n → ℕ)
    (cap : ℕ) (target : Fin n) (k : ℕ) {u : Fin n} (p : DWalk u target)
    (hp : Allowed (fun a b => edge a b=true) p) (hlen : p.length ≤ k) :
    value edge weight cap target k u ≤ walkCost weight p := by
  induction k generalizing u with
  | zero =>
    cases p with
    | nil => simp
    | cons h p => simp at hlen
  | succ k ih =>
    cases p with
    | nil =>
      exact (value_succ_le _ _ _ _ _ _).trans (ih .nil (allowed_nil _ _) (by simp))
    | @cons u v target h p =>
      have hh := (allowed_cons _ h p).mp hp
      have htail := ih p hh.2 (by simpa using Nat.le_of_succ_le_succ hlen)
      rw [walkCost_cons]
      exact (value_le_step edge weight cap target u v k h.ne hh.1).trans (Nat.add_le_add_left htail _)

end GreedyShortcuts.FiniteDistanceDP
