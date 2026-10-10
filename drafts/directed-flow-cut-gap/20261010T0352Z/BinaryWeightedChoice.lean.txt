import DirectedFlowCutGap.BinaryDivision
import DirectedFlowCutGap.IntegerWeightedChoice

/-!
# Binary prefix-mass selection with literal label copying

This program compares the retained ticket bits with each retained integer mass,
subtracts that mass when advancing, and copies the chosen binary label. It never
decodes an integer or expands a mass into tickets during execution. Leading-zero
padding is accepted. Natural denotations occur only in the refinement proof.

The bound pays the actual binary comparisons/subtractions, list traversal and
selected label copy. Construction of the mass list, a fair-bit ticket draw and
the subsequent lookup of a selected cut are separate composition obligations.
-/
namespace DirectedFlowCutGap.BinaryWeightedChoice
open BinaryArithmetic

def copyBits : Bits → Bits × ℕ
  | [] => ([],1)
  | b::bs => let r := copyBits bs; (b::r.1,r.2+4)

theorem copyBits_spec (bs : Bits) :
    (copyBits bs).1 = bs ∧ (copyBits bs).2 = 4*bs.length+1 := by
  induction bs with
  | nil => simp [copyBits]
  | cons b bs ih => simp [copyBits,ih.1,ih.2]; omega

def choose : List (Bits × Bits) → Bits → Option Bits × ℕ
  | [], _ => (none,1)
  | (label,mass)::xs, ticket =>
      let c := BinaryArithmetic.compare ticket mass
      if c.less then
        let l := copyBits label
        (some l.1,c.steps+l.2+8)
      else
        let d := BinaryDivision.sub ticket mass
        let r := choose xs d.1
        (r.1,c.steps+d.2+r.2+8)

/-- The fixed execution relation exposes the actually reached binary branches. -/
inductive ChooseExec : List (Bits × Bits) → Bits → Option Bits → ℕ → Prop
  | empty (ticket : Bits) : ChooseExec [] ticket none 1
  | found (label mass ticket : Bits) (xs : List (Bits × Bits)) :
      (BinaryArithmetic.compare ticket mass).less = true →
      ChooseExec ((label,mass)::xs) ticket (some (copyBits label).1)
        ((BinaryArithmetic.compare ticket mass).steps+(copyBits label).2+8)
  | next (label mass ticket : Bits) (xs : List (Bits × Bits))
      (out : Option Bits) (q : ℕ) :
      (BinaryArithmetic.compare ticket mass).less = false →
      ChooseExec xs (BinaryDivision.sub ticket mass).1 out q →
      ChooseExec ((label,mass)::xs) ticket out
        ((BinaryArithmetic.compare ticket mass).steps+(BinaryDivision.sub ticket mass).2+q+8)

theorem choose_exec (xs : List (Bits × Bits)) (ticket : Bits) :
    ChooseExec xs ticket (choose xs ticket).1 (choose xs ticket).2 := by
  induction xs generalizing ticket with
  | nil => exact .empty ticket
  | cons x xs ih =>
      rcases x with ⟨label,mass⟩
      cases hc : (BinaryArithmetic.compare ticket mass).less
      · simpa [choose,hc] using ChooseExec.next label mass ticket xs _ _ hc
          (ih (BinaryDivision.sub ticket mass).1)
      · simpa [choose,hc] using ChooseExec.found label mass ticket xs hc

def meaning (xs : List (Bits × Bits)) : List (ℕ × ℕ) :=
  xs.map fun x => (value x.1,value x.2)

theorem choose_refines (xs : List (Bits × Bits)) (ticket : Bits) :
    (choose xs ticket).1.map value = IntegerWeightedChoice.choose (meaning xs) (value ticket) := by
  induction xs generalizing ticket with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨label,mass⟩
      have hc := (compare_spec ticket mass).1
      have hs := (BinaryDivision.sub_spec ticket mass).1
      cases hb : (BinaryArithmetic.compare ticket mass).less
      · have hn : ¬ value ticket < value mass := by simpa [hb] using hc
        simpa [choose,meaning,hb,IntegerWeightedChoice.choose,hn,hs] using
          ih (BinaryDivision.sub ticket mass).1
      · have hl : value ticket < value mass := hc.mp hb
        simp [choose,meaning,hb,IntegerWeightedChoice.choose,hl,(copyBits_spec label).1]

theorem sub_length_le (ticket mass : Bits) :
    (BinaryDivision.sub ticket mass).1.length ≤ ticket.length := by
  rw [(BinaryDivision.sub_spec ticket mass).2.1]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.size_le.mpr (value_lt ticket))

/-- A bound in actual stored mass/ticket and label widths, including padding. -/
theorem choose_bound (xs : List (Bits × Bits)) (ticket : Bits) (B C : ℕ)
    (ht : ticket.length ≤ B)
    (hx : ∀ x ∈ xs, x.1.length ≤ C ∧ x.2.length ≤ B) :
    (choose xs ticket).2 ≤ xs.length * (160*(B+1)+4*C+16)+1 := by
  induction xs generalizing ticket with
  | nil => simp [choose]
  | cons x xs ih =>
      rcases x with ⟨label,mass⟩
      obtain ⟨hl,hm⟩ := hx (label,mass) List.mem_cons_self
      have hc := (compare_spec ticket mass).2.2
      have hmax : max ticket.length mass.length ≤ B := max_le ht hm
      cases hb : (BinaryArithmetic.compare ticket mass).less
      · have hs := (BinaryDivision.sub_spec ticket mass).2.2
        have hi := ih (BinaryDivision.sub ticket mass).1
          ((sub_length_le ticket mass).trans ht)
          (fun y hy => hx y (List.mem_cons_of_mem (label,mass) hy))
        simp only [choose,hb,Bool.false_eq_true,ite_false,List.length_cons]
        nlinarith
      · have hcopy := (copyBits_spec label).2
        simp only [choose,hb,ite_true,List.length_cons]
        nlinarith

end DirectedFlowCutGap.BinaryWeightedChoice
