import DirectedFlowCutGap.CachedBinaryIndex
import DirectedFlowCutGap.CachedHeapWidths

/-! Execute the scalar calculations of a cached read with binary operations.
The old work observation is retained. The new field counts the calculations
at the proved widths, including the three indexed reads. -/
namespace DirectedFlowCutGap.CachedScalarRead

open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceHeap (Store)
open CachedBinaryIndex (Indexes compute)
open CachedHeapWidths (readerWidth)

private def addMeasured (x y : ℕ) : ℕ × ℕ :=
  let left := BinaryNaturalView.encode x
  let right := BinaryNaturalView.encode y
  let sum := addCanonical left.1 right.1
  let result := BinaryNaturalView.decode sum.1
  (result.1,left.2+right.2+sum.2+result.2+4)

private theorem add_value (x y : ℕ) : (addMeasured x y).1=x+y := by
  simp only [addMeasured,BinaryNaturalView.decode_value,(canonical_values ..).1,BinaryNaturalView.encode_value]

private theorem add_paid {B x y : ℕ} (hx : x.size≤B) (hy : y.size≤B) : (addMeasured x y).2≤96*(B+2)^2 := by
  let l := BinaryNaturalView.encode x
  let r := BinaryNaturalView.encode y
  let added := addCanonical l.1 r.1
  have lwidth : l.1.length≤B := by rw [show l.1=x.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]; exact hx
  have rwidth : r.1.length≤B := by rw [show r.1=y.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]; exact hy
  have work := (canonical_charges lwidth rwidth).1
  have w := (canonical_values l.1 r.1).2.2.1
  rw [show value l.1=x from BinaryNaturalView.encode_value _,show value r.1=y from BinaryNaturalView.encode_value _] at w
  have fits : (x+y).size≤B+1 := Nat.size_le.mpr (by
    have xl := Nat.size_le.mp hx
    have yl := Nat.size_le.mp hy
    rw [pow_succ]
    omega)
  have cap {n : ℕ} (le : n≤B+1) : 16*(n+1)^2≤16*(B+2)^2 :=
    Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right le 1) 2)
  have wl := (BinaryNaturalView.encode_paid x).trans (cap (hx.trans (Nat.le_succ _)))
  have wr := (BinaryNaturalView.encode_paid y).trans (cap (hy.trans (Nat.le_succ _)))
  have wd := (BinaryNaturalView.decode_paid added.1).trans (cap (w.le.trans fits))
  change l.2+r.2+added.2+(BinaryNaturalView.decode added.1).2+4≤_
  nlinarith only [wl,wr,work,wd,Nat.zero_le B,Nat.zero_le (B^2)]

def sumMeasured : List ℕ → ℕ × ℕ
  | [] => (0,1)
  | x::xs =>
      let rest := sumMeasured xs
      let combined := addMeasured x rest.1
      (combined.1,combined.2+rest.2+4)

theorem sum_value (values : List ℕ) : (sumMeasured values).1=values.sum := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp only [sumMeasured,add_value,ih,List.sum_cons]

theorem sum_paid {B : ℕ} (values : List ℕ) (width : values.sum.size≤B) :
    (sumMeasured values).2≤values.length*(96*(B+2)^2+4)+1 := by
  induction values with
  | nil => simp [sumMeasured]
  | cons x xs ih =>
      simp only [List.sum_cons] at width
      have left := (Nat.size_le_size (Nat.le_add_right x xs.sum)).trans width
      have right := (Nat.size_le_size (Nat.le_add_left xs.sum x)).trans width
      have step := add_paid left (show (sumMeasured xs).1.size≤B from by
        rw [sum_value]; exact right)
      have rest := ih right
      simp only [sumMeasured,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

private def fees (s : Store) (address : Bits) (index : Indexes) : List ℕ × ℕ :=
  let zero := isZero address
  let payload := s.cellPrefix[index.successor]?.getD 0
  if zero.1 then ([payload,zero.2,4],zero.2+3)
  else
    let prior := s.countPrefix[index.predecessor]?.getD 0
    let borrow := predecessor address
    ([payload,zero.2,borrow.2,6,prior,5],zero.2+borrow.2+6)

def read (s : Store) (address : Bits) : (Option (Cell Bits) × ℕ) × ℕ :=
  let index := compute s.cells.size address
  if index.inside then
    let amounts := fees s address index
    let total := sumMeasured amounts.1
    let loaded := s.cells[index.address]?
    let slots := s.cells.size.size+index.address.size+index.successor.size+index.predecessor.size+12
    ((loaded,total.1),index.work+amounts.2+total.2+slots)
  else (CachedReferenceHeap.read s address,index.work)

private theorem fee_value (s : Store) (address : Bits) (inside : value address<s.cells.size) :
    (fees s address (compute s.cells.size address)).1.sum=(CachedReferenceHeap.read s address).2 := by
  obtain ⟨_,next,prior,_⟩ := CachedBinaryIndex.values s.cells.size address
  unfold fees CachedReferenceHeap.read
  rw [ite_eq_left inside,next,prior]
  let a := (isZero address).2
  let b := (predecessor address).2
  let x := s.cellPrefix[value address+1]?.getD 0
  let y := s.countPrefix[value address-1]?.getD 0
  dsimp only
  by_cases z : (isZero address).1=true
  · have hv := (isZero_spec address).1.mp z
    rw [ite_eq_left z]
    change [x,a,4].sum=x+(if value address=0 then a+4 else a+b+6+y+5)
    simp only [ite_eq_left hv,List.sum_cons,List.sum_nil]
    omega
  · have hv := fun h => z ((isZero_spec address).1.mpr h)
    rw [ite_eq_right z]
    change [x,a,b,6,y,5].sum=x+(if value address=0 then a+4 else a+b+6+y+5)
    simp only [ite_eq_right hv,List.sum_cons,List.sum_nil]
    omega

theorem value_eq (s : Store) (address : Bits) : (read s address).1=CachedReferenceHeap.read s address := by
  obtain ⟨here,_,_,check⟩ := CachedBinaryIndex.values s.cells.size address
  by_cases inside : value address<s.cells.size
  · have branch := check.mpr inside
    unfold read
    simp only [ite_eq_left branch]
    apply Prod.ext
    · simp only [here,CachedReferenceHeap.read,ite_eq_left inside]
    · rw [sum_value,fee_value s address inside]
  · have branch := fun ready => inside (check.mp ready)
    simp only [read,ite_eq_right branch]

def budget (W : ℕ) : ℕ := 128*(W+2)^2+6*(96*(W+2)^2+4)+48*(W+1)+20

theorem paid {s : Store} {H B : ℕ} (cells : s.cells.size≤H)
    (bounded : Heap.Bounded B s.cells.toList) (address : Bits) (width : address.length≤B)
    (inside : value address<s.cells.size) :
    (read s address).2≤budget (readerWidth H B) := by
  let W := readerWidth H B
  let index := compute s.cells.size address
  let amounts := fees s address index
  obtain ⟨dimension,word,cached,indices⟩ := CachedHeapWidths.read_width cells bounded address width
  obtain ⟨here,next,prior,check⟩ := CachedBinaryIndex.values s.cells.size address
  have haveWidth : B≤W := le_max_left _ _
  have indexed := CachedBinaryIndex.paid address (width.trans haveWidth) dimension
  have oldWidth : amounts.1.sum.size≤W := by
    rw [show amounts.1.sum=(CachedReferenceHeap.read s address).2 from fee_value s address inside]
    exact cached
  have total := sum_paid amounts.1 oldWidth
  have sourceSteps : amounts.2≤36*(W+1)+6 := by
    unfold amounts fees
    have zero := (isZero_spec address).2
    have borrow := (predecessor_spec address).2.2
    have fit := width.trans haveWidth
    dsimp only
    split <;> dsimp only <;> omega
  have count : amounts.1.length≤6 := by
    unfold amounts fees
    dsimp only
    split <;> simp
  have totalCap := total.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ count) 1)
  have afterFits := (indices inside).1
  have beforeFits := (indices inside).2.1
  have branch := check.mpr inside
  unfold read
  simp only [ite_eq_left branch,here,next,prior]
  change index.work+amounts.2+(sumMeasured amounts.1).2+
    (s.cells.size.size+(value address).size+(value address+1).size+(value address-1).size+12)≤
      128*(W+2)^2+6*(96*(W+2)^2+4)+48*(W+1)+20
  change index.work≤128*(W+2)^2 at indexed
  omega

end DirectedFlowCutGap.CachedScalarRead
