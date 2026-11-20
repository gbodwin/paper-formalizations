import DirectedFlowCutGap.BinaryMaskPrefix
import DirectedFlowCutGap.EncodedArrayStorage

/-! Construct the typed boundary array from the measured cut bitword.
The copy certificate covers the retained Boolean payloads and the actual
array copy constructors. The fresh-cell estimate bounds every allocated
slot address before charging an address width. -/
namespace DirectedFlowCutGap.MaskBoundaryAssembly

open BinaryArithmetic
open EncodedRoundingInput (collect collect_size collect_value collect_work)
open EncodedArrayStorage (CollectExec collectTrace collectCells allocateTrace)

def items (n : ℕ) (word : Bits) : List (Bool × ℕ) :=
  (BinaryMaskPrefix.mask n word).1.map fun b => (b,0)

private theorem items_length (n : ℕ) (word : Bits) : (items n word).length=n := by
  simp only [items,List.length_map,(BinaryMaskPrefix.mask_spec n word).1,BinaryMaskPrefix.padded_length]

def run (n : ℕ) (word : Bits) : Vector Bool n × ℕ :=
  let bounded := BinaryMaskPrefix.mask n word
  let entries := bounded.1.map fun b => (b,0)
  let result := collect entries
  (⟨result.1,(collect_size (items n word)).trans (items_length n word)⟩,
    bounded.2+result.2+8*n+4)

theorem result_word (n : ℕ) (word : Bits) : (run n word).1.toList=BinaryMaskPrefix.padded n word := by
  change (collect (items n word)).1.toList= _
  rw [collect_value]
  simp only [items,List.map_map,Function.comp_def,(BinaryMaskPrefix.mask_spec n word).1]
  change List.map id (BinaryMaskPrefix.padded n word) = _
  simp

theorem result_at (n : ℕ) (word : Bits) :
    (run n word).1=Vector.ofFn (fun i : Fin n => word.toArray[i.val]?.getD false) := by
  apply Vector.ext
  intro i inside
  have i' : i < (run n word).1.toList.length := by simpa only [Vector.length_toList] using inside
  have exactBit : (run n word).1.toList[i]?.getD false=word[i]?.getD false := by
    rw [result_word]
    exact BinaryMaskPrefix.padded_lookup n word i inside
  simpa only [List.getElem?_eq_getElem i',Option.getD_some,Vector.getElem_toList,
    Vector.getElem_ofFn,List.getElem?_toArray] using exactBit

theorem paid_eq (n : ℕ) (word : Bits) :
    (run n word).2=(BinaryMaskPrefix.mask n word).2+n^2+15*n+5 := by
  have costs : (collect (items n word)).2=n^2+7*n+1 := by
    rw [collect_work,items_length]
    have zero : List.sum ((items n word).map Prod.snd)=0 := by
      simp only [items,List.map_map,Function.comp_def]
      induction (BinaryMaskPrefix.mask n word).1 <;> simp_all
    omega
  change (BinaryMaskPrefix.mask n word).2+(collect (items n word)).2+8*n+4=_
  omega

theorem paid (n : ℕ) (word : Bits) : (run n word).2≤16*(2*n+1)^2 := by
  rw [paid_eq]
  cases n with
  | zero => simp [BinaryMaskPrefix.mask_zero_paid]
  | succ n =>
    cases n with
    | zero => simp [BinaryMaskPrefix.mask_one_paid]
    | succ k =>
      have bound := (BinaryMaskPrefix.mask_spec (k+2) word).2
      change (BinaryMaskPrefix.mask (k+2) word).2+(k+2)^2+15*(k+2)+5≤16*(2*(k+2)+1)^2
      nlinarith only [bound,Nat.zero_le k,Nat.zero_le (k^2)]

theorem copy_instructions (n : ℕ) (word : Bits) :
    let inputs := items n word
    let trace := collectTrace inputs
    CollectExec inputs (run n word).1.toArray trace ∧
      trace.length=2*n^2+21*n+4 ∧ EncodedArrayStorage.fresh trace≤n^2+7*n+2 := by
  exact ⟨EncodedArrayStorage.collect_exec (items n word),
    (EncodedArrayStorage.collectTrace_length _).trans (by rw [items_length]),
    (EncodedArrayStorage.collectTrace_fresh _).le.trans (by
      rw [items_length]
      exact EncodedArrayStorage.collectCells_bound n)⟩

theorem copy_address_size (n inputCells : ℕ) (word : Bits) (block : ℕ × ℕ)
    (allocated : block ∈ (allocateTrace inputCells (collectTrace (items n word))).2)
    (offset : ℕ) (valid : offset<block.2) :
    (block.1+offset).size≤(inputCells+n^2+7*n+2).size := by
  have actual := EncodedArrayStorage.allocated_address (collectTrace (items n word)) inputCells block allocated offset
  have fresh := (copy_instructions n word).2.2
  have room : block.1+offset ≤ inputCells+n^2+7*n+2 := by omega
  exact Nat.size_le.mpr (room.trans_lt (Nat.lt_size_self _))

end DirectedFlowCutGap.MaskBoundaryAssembly
