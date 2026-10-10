import DirectedFlowCutGap.PackedBooleanConstructor

/-! Materialize an actual counter spine from an incoming binary word.
The executable recursion branches only on Boolean digits. Its copy loop and
packed-heap constructor both carry their declared primitive charges.
Compiling this constructor into the instruction language remains separate. -/
namespace DirectedFlowCutGap.BinaryCounterMaterialization
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def appendCopy : Bits → Bits → Bits × ℕ
  | [], ys => (ys,1)
  | x::xs, ys => let r := appendCopy xs ys; (x::r.1,r.2+2)

theorem appendCopy_spec (xs ys : Bits) :
    (appendCopy xs ys).1=xs++ys ∧ (appendCopy xs ys).2=2*xs.length+1 := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih => simp [appendCopy,ih.1,ih.2]; omega

def expand : Bits → Bits × ℕ
  | [] => ([],1)
  | b::bs =>
      let r := expand bs
      let doubled := appendCopy r.1 r.1
      if b then (false::doubled.1,r.2+doubled.2+3)
      else (doubled.1,r.2+doubled.2+2)

theorem expand_spec (word : Bits) :
    (expand word).1.length=value word ∧
    (expand word).2≤4*value word+4*word.length+1 := by
  induction word with
  | nil => exact ⟨rfl,by decide⟩
  | cons b bs ih =>
      have hd := appendCopy_spec (expand bs).1 (expand bs).1
      cases b <;> simp only [expand,Bool.false_eq_true,ite_false,ite_true,
        hd.1,hd.2,List.length_append,List.length_cons,value,
        Bool.toNat_false,Bool.toNat_true,ih.1] <;> constructor <;> omega

def prepare (word : Bits) : Prepared :=
  let expanded := expand word
  let built := construct expanded.1
  { built with operations := expanded.2+built.operations+4 }

theorem prepare_spec (word : Bits) :
    (prepare word).heap.length=2*value word+1 ∧
    value (prepare word).next=(prepare word).heap.length ∧
    value (prepare word).root=2*value word ∧
    IndexSpine (eraseHeap (prepare word).heap) (value (prepare word).root) (value word) ∧
    BoolList (eraseHeap (prepare word).heap) 0 [] ∧
    (prepare word).next.length≤2*value word+1 ∧
    (prepare word).root.length≤2*value word+1 ∧
    (prepare word).heap.Bounded (2*value word+1) ∧
    (prepare word).operations≤128*(value word+1)^3+4*value word+4*word.length+5 := by
  have h := construct_valid (expand word).1
  have he := expand_spec word
  have hc := construct_charge (expand word).1
  have spine := boolList_spine h.table
  have nilSpine := h.suffix 0 (Nat.zero_le _)
  have nilTable : BoolList (eraseHeap (construct (expand word).1).heap) 0 [] := by
    cases nilSpine with
    | nil hn => exact .nil hn
  simp only [he.1] at hc spine
  refine ⟨by simpa [prepare,he.1] using h.heap_length,
    h.next_value.trans h.heap_length.symm,
    by simpa [prepare,he.1] using h.root_value,spine,nilTable,
    by simpa [prepare,he.1] using h.next_width,
    by simpa [prepare,he.1] using h.root_width,
    by simpa [prepare,he.1] using h.heap_bound,?_⟩
  simp only [prepare]
  omega

end DirectedFlowCutGap.BinaryCounterMaterialization
