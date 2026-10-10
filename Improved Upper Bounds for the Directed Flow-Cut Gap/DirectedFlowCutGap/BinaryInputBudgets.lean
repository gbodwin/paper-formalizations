import DirectedFlowCutGap.BinaryArithmetic

/-! Construct resource and stored-width words by scanning the actual input
lists. Binary increments/additions compute all returned words; natural counts
are specifications and ghost annotations only. Heap/address compilation of
these scans remains separate from their Boolean/list primitive accounting. -/
namespace DirectedFlowCutGap.BinaryInputBudgets
open BinaryArithmetic

def lengthWord {A : Type} : List A → Bits × ℕ
  | [] => ([],1)
  | _::xs => let r := lengthWord xs;let next := increment true r.1
              (next.1,r.2+next.2+4)

theorem lengthWord_spec {A : Type} (xs : List A) :
    value (lengthWord xs).1=xs.length ∧ (lengthWord xs).1.length ≤ xs.length ∧
    (lengthWord xs).2 ≤ 12*(xs.length+1)^2 := by
  induction xs with
  | nil => simp [lengthWord,value]
  | cons x xs ih =>
      have h := increment_spec true (lengthWord xs).1
      simp only [lengthWord,List.length_cons,Bool.toNat_true] at h ⊢
      refine ⟨by omega,by omega,?_⟩
      nlinarith [h.2.2]

def inputSize : List (Bits × Bits) → ℕ
  | [] => 0
  | (a,b)::xs => a.length+b.length+1+inputSize xs

def storedSize : List (Bits × Bits) → ℕ
  | [] => 0
  | (a,b)::xs => a.length+b.length+storedSize xs

structure Words where
  resources : Bits
  width : Bits
  operations : ℕ
  deriving Repr

def scan : List (Bits × Bits) → Words
  | [] => ⟨[],[],1⟩
  | (a,b)::xs =>
      let tail := scan xs
      let na := lengthWord a
      let nb := lengthWord b
      let subtotal := add false na.1 nb.1
      let total := add false subtotal.1 tail.width
      let count := increment true tail.resources
      ⟨count.1,total.1,tail.operations+na.2+nb.2+subtotal.2+total.2+count.2+12⟩

theorem sizes (xs : List (Bits × Bits)) :
    storedSize xs+xs.length=inputSize xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [storedSize,inputSize,List.length_cons];omega

theorem scan_spec (xs : List (Bits × Bits)) :
    value (scan xs).resources=xs.length ∧ value (scan xs).width=storedSize xs ∧
    (scan xs).resources.length ≤ inputSize xs ∧
    (scan xs).width.length ≤ 2*inputSize xs ∧
    (scan xs).operations ≤ 128*(inputSize xs+1)^2 := by
  induction xs with
  | nil => exact ⟨rfl,rfl,by decide,by decide,by decide⟩
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      have ha := lengthWord_spec a
      have hb := lengthWord_spec b
      have hs := add_spec false (lengthWord a).1 (lengthWord b).1
      have ht := add_spec false (add false (lengthWord a).1 (lengthWord b).1).1 (scan xs).width
      have hn := increment_spec true (scan xs).resources
      have hm : max (lengthWord a).1.length (lengthWord b).1.length ≤ a.length+b.length :=
        max_le (by omega) (by omega)
      have hmt : max (add false (lengthWord a).1 (lengthWord b).1).1.length
          (scan xs).width.length ≤ a.length+b.length+1+2*inputSize xs :=
        max_le (by omega) (by omega)
      simp only [scan,inputSize,List.length_cons,storedSize,Bool.toNat_false,Bool.toNat_true] at hs ht hn ⊢
      refine ⟨by omega,by omega,by omega,by omega,?_⟩
      nlinarith [hs.2.2,ht.2.2,hn.2.2]

theorem fields_bounded {xs : List (Bits × Bits)} {a b : Bits} (h : (a,b)∈xs) :
    a.length ≤ storedSize xs ∧ b.length ≤ storedSize xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rcases x with ⟨c,d⟩
      rcases List.mem_cons.mp h with he | ht
      · cases he; simp only [storedSize];omega
      · have hh := ih ht
        simp only [storedSize]
        omega

end DirectedFlowCutGap.BinaryInputBudgets
