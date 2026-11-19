import DirectedFlowCutGap.PhysicalEpochDraws

/-! The physical prefix swaps implement the retained epoch permutation. -/

namespace DirectedFlowCutGap.EpochPermutationData

open FinitePermutationSampler (Tape)
open PhysicalEpochDraws (permutationValues)

inductive Valid : List ℕ → ℕ → Prop
  | nil : Valid [] 0
  | cons {j js n} : j<n+1 → Valid js n → Valid (j::js) (n+1)

theorem valid_length {js : List ℕ} {n : ℕ} (valid : Valid js n) : js.length=n := by
  induction valid with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem valid_bound {js : List ℕ} {n : ℕ} (valid : Valid js n) {j : ℕ} (mem : j ∈ js) : j<n := by
  induction valid with
  | nil => simp at mem
  | cons first _ ih =>
    rcases List.mem_cons.mp mem with rfl | rest
    · exact first
    · exact (ih rest).trans (Nat.lt_succ_self _)

theorem values_valid (n : ℕ) (t : Tape n) : Valid (permutationValues n t) n := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rcases t with ⟨first,tail⟩
    exact .cons first.isLt (ih tail)

def suffix {α : Type*} (head : α) (tail : List α) (j : ℕ) : List α :=
  ((head::tail).set j head).tail

@[simp] theorem suffix_length {α : Type*} (head : α) (tail : List α) (j : ℕ) :
    (suffix head tail j).length=tail.length := by simp [suffix,List.length_tail]

def reorder {α : Type*} : List ℕ → List α → Option (List α)
  | [],[] => some []
  | j::js,head::tail => do
    let item ← (head::tail)[j]?
    let rest ← reorder js (suffix head tail j)
    pure (item::rest)
  | _,_ => none

theorem suffix_get {α : Type*} (head : α) (tail : List α)
    (j : Fin (tail.length+1)) (i : Fin tail.length) :
    (suffix head tail j.val)[i.val]'(by rw [suffix_length]; exact i.isLt) =
      (head::tail)[(Equiv.swap 0 j i.succ).val]'(Equiv.swap 0 j i.succ).isLt := by
  by_cases same : i.succ=j
  · rw [same,Equiv.swap_apply_right]
    have slot : j.val=i.val+1 := (congrArg Fin.val same).symm
    simp [suffix,slot]
  · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) same]
    have distinct : i.val+1≠j.val := fun eq => same (Fin.ext eq)
    simpa only [suffix,List.getElem_tail,Fin.val_succ] using
      (List.getElem_set_ne distinct.symm (a:=head) (l:=head::tail) (by simp [i.isLt]))

theorem reorder_tape {α : Type*} (n : ℕ) (t : Tape n) (xs : List α) (len : xs.length=n) :
    reorder (permutationValues n t) xs=some ((FinitePermutationSampler.run n t).order.map
      (fun i => xs[i.val]'(len ▸ i.isLt))) := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons x xs => simp at len
  | succ n ih =>
    rcases t with ⟨j,t⟩
    cases xs with
    | nil => simp at len
    | cons head tail =>
      have tl : tail.length=n := by simpa using len
      subst n
      let ys := suffix head tail j.val
      have ylen : ys.length=tail.length := suffix_length head tail j.val
      have inside : j.val<(head::tail).length := j.isLt
      have h := ih t ys ylen
      have map_tail (is : List (Fin tail.length)) :
          is.map (fun i => ys[i.val]'(by rw [ylen]; exact i.isLt)) =
            (is.map (fun i => Equiv.swap 0 j i.succ)).map
              (fun i => (head::tail)[i.val]'i.isLt) := by
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => suffix_get head tail j i)
      simp only [permutationValues,reorder,List.getElem?_eq_getElem inside]
      change (do
        let rest ← reorder (permutationValues tail.length t) ys
        pure ((head::tail)[j.val]::rest))=_
      rw [h]
      simp only [pure,FinitePermutationSampler.run,FinitePermutationSampler.scan_list,List.map_cons]
      rw [map_tail]
      rfl

end DirectedFlowCutGap.EpochPermutationData
