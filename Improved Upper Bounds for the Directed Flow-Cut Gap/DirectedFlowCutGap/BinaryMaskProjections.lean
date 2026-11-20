import DirectedFlowCutGap.BinaryMaskScans
import DirectedFlowCutGap.BinaryArrayBatch

/-! Execute the retained-index scans and fill the projected destination in
order. The returned fee is exactly the earlier fee for the same pullback. -/
namespace DirectedFlowCutGap.BinaryMaskProjections

open EncodedUnitCostPreparation (Prepared)
open EncodedUnitCostReplication
open CachedScalarRead (sumMeasured sum_value sum_paid)

private def indices {N : ℕ} (selected : Vector Bool N) (start : ℕ) : List (Fin N) :=
  (BinaryIndexList.checkedMask selected start).1.get (by rw [BinaryIndexList.checkedMask_value]; rfl)

private theorem indices_value {N : ℕ} (selected : Vector Bool N) (start : ℕ) :
    indices selected start=retainedIndices selected := by
  unfold indices
  exact Option.get_of_eq_some _ (BinaryIndexList.checkedMask_value selected start)

private def project {m N : ℕ} (selected : Vector Bool N) (start : ℕ)
    (test : List (Fin N) → Fin m → (Bool × ℕ) × ℕ) : (Vector Bool m × ℕ) × ℕ :=
  let listed := BinaryIndexList.checkedMask selected start
  let cursor := listed.1.get (by
    change (BinaryIndexList.checkedMask selected start).1.isSome
    rw [BinaryIndexList.checkedMask_value]
    rfl)
  let batch := BinaryArrayBatch.runWithChildWork (test cursor)
  let rows := BinaryNaturalOperations.mul m 11
  let cells := BinaryNaturalOperations.mul selected.toArray.size 14
  let fee := sumMeasured [batch.1.2,rows.1,cells.1,6]
  ((batch.1.1,fee.1),listed.2+batch.2+rows.2+cells.2+fee.2+4)

private theorem batch_fee {m N per : ℕ} {selected : Vector Bool N} {start : ℕ}
    (test : List (Fin N) → Fin m → (Bool × ℕ) × ℕ)
    (fee : ∀ is i, (test is i).1.2=per*is.length+1) :
    (BinaryArrayBatch.runWithChildWork (test (indices selected start))).1.2=
      m*(per*N+1)+8*m+4 := by
  rw [BinaryArrayBatch.runWithChildWork_value]
  simp only [List.map_ofFn,Function.comp_def,fee,indices_value,BinaryIndexList.retained_length,
    List.ofFn_const,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

private theorem project_value {m N per : ℕ} (selected : Vector Bool N) (start : ℕ)
    (test : List (Fin N) → Fin m → (Bool × ℕ) × ℕ)
    (fee : ∀ is i, (test is i).1.2=per*is.length+1) :
    (project selected start test).1=
      (Vector.ofFn (fun i => (test (retainedIndices selected) i).1.1),m*(per*N+20)+14*N+10) := by
  let batch := BinaryArrayBatch.runWithChildWork (test (indices selected start))
  apply Prod.ext
  · change batch.1.1=_
    simp only [batch,BinaryArrayBatch.runWithChildWork_value,indices_value]
  · change (sumMeasured [batch.1.2,(BinaryNaturalOperations.mul m 11).1,
        (BinaryNaturalOperations.mul selected.toArray.size 14).1,6]).1=_
    simp only [batch,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,batch_fee test fee,
      BinaryNaturalOperations.mul_value,Vector.size_toArray]
    ring

def budget {R : Type*} [Semiring R] (m N per B : R) : R :=
  BinaryIndexList.checkedBudget N B+
    BinaryArrayBatch.childCeiling m (per*N+1) (N*BinaryMaskScans.scanBudget B+1)+
    2*(BinaryRawRational.budget B+4)+4*(96*(B+2)^2+4)+5

private theorem project_paid {m N per B : ℕ} (selected : Vector Bool N) (start : ℕ)
    (test : List (Fin N) → Fin m → (Bool × ℕ) × ℕ)
    (fee : ∀ is i, (test is i).1.2=per*is.length+1)
    (child : ∀ i, (test (retainedIndices selected) i).2 ≤ N*BinaryMaskScans.scanBudget B+1)
    (width : N.size≤B) (address : (start+2*N).size≤B)
    (total : (m*(per*N+20)+14*N+20).size≤B) :
    (project selected start test).2 ≤ budget m N per B := by
  let batch := BinaryArrayBatch.runWithChildWork (test (indices selected start))
  let rows := BinaryNaturalOperations.mul m 11
  let cells := BinaryNaturalOperations.mul selected.toArray.size 14
  let fees := [batch.1.2,rows.1,cells.1,6]
  have listed := BinaryIndexList.checkedMask_paid selected start width address
  have each (i : Fin m) : (test (indices selected start) i).1.2 ≤ per*N+1 := by
    rw [fee,indices_value,BinaryIndexList.retained_length]
  have step (i : Fin m) : (test (indices selected start) i).2 ≤ N*BinaryMaskScans.scanBudget B+1 := by
    rw [indices_value]
    exact child i
  have filled : batch.2≤BinaryArrayBatch.childCeiling m (per*N+1) (N*BinaryMaskScans.scanBudget B+1) :=
    (BinaryArrayBatch.runWithChildWork_paid _ each step).trans (BinaryArrayBatch.childBudget_le ..)
  have fits {x : ℕ} (h : x ≤ m*(per*N+20)+14*N+20) : x.size≤B := (Nat.size_le_size h).trans total
  have rowFits : m.size≤B := fits (by
    have h := Nat.mul_le_mul_left m (show 1≤per*N+20 by omega)
    simp only [Nat.mul_one] at h
    omega)
  have eleven : (11 : ℕ).size≤B := fits (by omega)
  have fourteen : (14 : ℕ).size≤B := fits (by omega)
  have rowWork : rows.2≤BinaryRawRational.budget B+4 := BinaryNaturalOperations.mul_paid rowFits eleven
  have cellWork : cells.2≤BinaryRawRational.budget B+4 :=
    BinaryNaturalOperations.mul_paid (by simpa only [Vector.size_toArray] using width) fourteen
  have sumFits : fees.sum.size≤B := fits (by
    simp only [fees,batch,rows,cells,batch_fee test fee,BinaryNaturalOperations.mul_value,
      Vector.size_toArray,List.sum_cons,List.sum_nil,Nat.add_zero]
    nlinarith)
  have summed : (sumMeasured fees).2≤4*(96*(B+2)^2+4)+1 := sum_paid fees sumFits
  change (BinaryIndexList.checkedMask selected start).2+batch.2+rows.2+cells.2+(sumMeasured fees).2+4≤_
  unfold budget
  omega

def core {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) (start : ℕ) :
    (Vector Bool n × ℕ) × ℕ :=
  project selected start fun is v => BinaryMaskScans.core out selected v is

theorem core_value {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) (start : ℕ) :
    (core out selected start).1=out.pullbackMaskWithCost selected := by
  have fee (is : List (Fin out.size)) (v : Fin n) :
      (BinaryMaskScans.core out selected v is).1.2=20*is.length+1 := by
    rw [BinaryMaskScans.core_value,Prepared.coreScan_work]
  rw [core,project_value selected start _ fee]
  simp only [BinaryMaskScans.core_value,Prepared.pullbackMaskWithCost,Prepared.pullbackMask,Vector.size_toArray]

theorem core_paid {n B : ℕ} (out : Prepared n) (selected : Vector Bool out.size) (start : ℕ)
    (width : out.size.size≤B) (address : (start+2*out.size).size≤B)
    (port : (3*n).size≤B) (scan : (out.size*20+1).size≤B) (step : (20 : ℕ).size≤B)
    (total : (n*(20*out.size+20)+14*out.size+20).size≤B) :
    (core out selected start).2≤budget n out.size 20 B := by
  apply project_paid selected start
  · intro is v
    rw [BinaryMaskScans.core_value,Prepared.coreScan_work]
  · intro v
    have work := BinaryMaskScans.core_paid out selected v (retainedIndices selected)
      (BinaryIndexList.retained_length selected).le width port scan step
    rwa [BinaryIndexList.retained_length] at work
  · exact width
  · exact address
  · exact total

def fiber {m N : ℕ} {k : Vector ℕ m} (labels : Vector (Clone k) N) (selected : Vector Bool N) (start : ℕ) :
    (Vector Bool m × ℕ) × ℕ :=
  project selected start fun is v => BinaryMaskScans.fiber labels selected v is

theorem fiber_value {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (start : ℕ) :
    (fiber labels selected start).1=fullFiberMaskWithCost k labels selected := by
  have fee (is : List (Fin N)) (v : Fin m) :
      (BinaryMaskScans.fiber labels selected v is).1.2=9*is.length+1 := by
    rw [BinaryMaskScans.fiber_value k,fiberScan_work]
  rw [fiber,project_value selected start _ fee]
  simp only [BinaryMaskScans.fiber_value k,fullFiberMaskWithCost,fullFiberMask,Vector.size_toArray]

theorem fiber_paid {m N B : ℕ} {k : Vector ℕ m} (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (start : ℕ) (width : N.size≤B) (address : (start+2*N).size≤B)
    (label : m.size≤B) (scan : (N*9+1).size≤B) (step : (9 : ℕ).size≤B)
    (total : (m*(9*N+20)+14*N+20).size≤B) :
    (fiber labels selected start).2≤budget m N 9 B := by
  apply project_paid selected start
  · intro is v
    rw [BinaryMaskScans.fiber_value k,fiberScan_work]
  · intro v
    have work := BinaryMaskScans.fiber_paid labels selected v (retainedIndices selected)
      (BinaryIndexList.retained_length selected).le width label scan step
    rwa [BinaryIndexList.retained_length] at work
  · exact width
  · exact address
  · exact total

end DirectedFlowCutGap.BinaryMaskProjections
