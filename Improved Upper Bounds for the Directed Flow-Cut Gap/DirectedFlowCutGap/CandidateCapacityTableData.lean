import DirectedFlowCutGap.CandidateNodeListsProgram
import DirectedFlowCutGap.CandidateCapacityValues

/-! Identify the stored descriptor order and exact capacity matrix. -/

namespace DirectedFlowCutGap.CandidateCapacityTableData

open BinaryArithmetic CandidateEnumeration
open CandidateNodeListsProgram (levelBlock portBlock blocks_eq_order taggedPort)
open CandidatePortAdjacencyProgram (Kind)
open CandidatePhysicalCut (networkSize capacities numberEquiv capacityWidth)
open ResidualZeroTableProgram (CapacityValues)
open EncodedCandidateCapacity (Input)

private theorem fin_indices (n start : ℕ) :
    (List.finRange n).map (fun v => start+v.val)=List.range' start n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_range']

private theorem level_indices {n L : ℕ} (p : Port n) (side : Bool) :
    (levelBlock p side (List.finRange (L+1))).map networkIndex =
      List.range' (pointIndex (p,side)*(L+1)) (L+1) := by
  simp only [levelBlock,List.map_map,Function.comp_def,networkIndex,nodeIndex]
  exact fin_indices (L+1) (pointIndex (p,side)*(L+1))

private theorem pair_indices {n L : ℕ} (p : Port n) :
    (levelBlock p false (List.finRange (L+1))++levelBlock p true (List.finRange (L+1))).map networkIndex =
      List.range' (portIndex p*(2*(L+1))) (2*(L+1)) := by
  rw [List.map_append,level_indices,level_indices]
  let k := L+1
  let start := portIndex p*(2*k)
  have a : pointIndex (p,false)*k=start := by simp [pointIndex,start]; ring
  have b : pointIndex (p,true)*k=start+k := by simp [pointIndex,start]; ring
  change List.range' (pointIndex (p,false)*k) k ++ List.range' (pointIndex (p,true)*k) k =
      List.range' start (2*k)
  rw [a,b,List.range'_append_1,show k+k=2*k by omega]

private theorem range_chunks (start count size : ℕ) :
    (List.range' start count).flatMap (fun i => List.range' (i*size) size)=
      List.range' (start*size) (count*size) := by
  induction count generalizing start with
  | zero => simp
  | succ remaining ih =>
    rw [List.range'_succ,List.flatMap_cons,ih]
    rw [show (start+1)*size=start*size+size by ring,List.range'_append_1]
    rw [Nat.succ_mul,Nat.add_comm]

def portOffset (n : ℕ) : Kind→ℕ
  | .core => 0
  | .start => n
  | .finish => 2*n

private theorem port_indices {n L : ℕ} (k : Kind) :
    (portBlock k (List.finRange n) (List.finRange (L+1))).map networkIndex =
      List.range' (portOffset n k*(2*(L+1))) (n*(2*(L+1))) := by
  simp only [portBlock,List.map_flatMap,pair_indices]
  have same (v : Fin n) : portIndex (taggedPort k v)=portOffset n k+v.val := by
    cases k <;> simp [taggedPort,portIndex,portOffset]
  simp only [same]
  rw [← range_chunks,← fin_indices,List.flatMap_map]

theorem order_indices (n L : ℕ) : (networkOrder n L).map networkIndex=List.range (networkSize n L) := by
  rw [← blocks_eq_order]
  simp only [List.map_append,port_indices,portOffset,List.map_cons,List.map_nil,networkIndex,ite_false,ite_true,
    Bool.false_eq_true,Nat.zero_mul,Nat.add_zero,List.range_eq_range',networkSize]
  let k := n*(2*(L+1))
  have q : 2*n*(2*(L+1))=k+k := by unfold k; ring
  have p : 6*n*(L+1)=k+k+k := by unfold k; ring
  rw [q,p]
  change ((List.range' 0 k++List.range' k k)++List.range' (k+k) k)++[k+k+k,k+k+k+1]=
    List.range' 0 (k+k+k+2)
  have first : List.range' 0 k++List.range' k k=List.range' 0 (k+k) := by simpa using List.range'_append_1 (s:=0) (m:=k) (n:=k)
  have second : List.range' 0 (k+k)++List.range' (k+k) k=List.range' 0 (k+k+k) := by
    simpa using List.range'_append_1 (s:=0) (m:=k+k) (n:=k)
  have third : List.range' 0 (k+k+k)++List.range' (k+k+k) 2=List.range' 0 (k+k+k+2) := by
    simpa using List.range'_append_1 (s:=0) (m:=k+k+k) (n:=2)
  rw [first,second]
  exact third

theorem numbered_order (n L : ℕ) : (networkOrder n L).map (numberEquiv n L)=List.finRange (networkSize n L) := by
  apply (List.map_injective_iff (f:= (Fin.val : Fin (networkSize n L) → ℕ))).mpr Fin.val_injective
  simp only [List.map_map,Function.comp_def,CandidatePhysicalCut.numberEquiv_value,order_indices,List.range_eq_range']
  simpa using (fin_indices (networkSize n L) 0).symm

variable {n : ℕ}

noncomputable def row (D : Input n) (s t : Fin n) (L B : ℕ) (a : Network n L)
    (bs : List (Network n L)) : List Bits :=
  bs.map fun b => (capacities D s t L B (numberEquiv n L a) (numberEquiv n L b)).bits

noncomputable def table (D : Input n) (s t : Fin n) (L B : ℕ) (as bs : List (Network n L)) : List (List Bits) :=
  as.map fun a => row D s t L B a bs

theorem table_values (D : Input n) (s t : Fin n) (L B : ℕ) :
    CapacityValues (capacities D s t L B) (table D s t L B (networkOrder n L) (networkOrder n L))
      (List.finRange (networkSize n L)) (List.finRange (networkSize n L)) := by
  have row_values (a : Network n L) (bs : List (Network n L)) :
      List.Forall₂ (fun word v => value word=capacities D s t L B (numberEquiv n L a) v)
        (row D s t L B a bs) (bs.map (numberEquiv n L)) := by
    induction bs with
    | nil => exact .nil
    | cons b bs ih => exact .cons (value_bits _) ih
  have rows (as bs : List (Network n L)) :
      CapacityValues (capacities D s t L B) (table D s t L B as bs) (as.map (numberEquiv n L)) (bs.map (numberEquiv n L)) := by
    induction as with
    | nil => exact .nil
    | cons a as ih => exact .cons (row_values a bs) ih
  simpa only [numbered_order] using rows (networkOrder n L) (networkOrder n L)

theorem table_widths (D : Input n) (s t : Fin n) (L B : ℕ) (as bs : List (Network n L)) :
    ∀ a ∈ table D s t L B as bs,∀ w ∈ a,w.length ≤ capacityWidth n L := by
  intro a ha w hw
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hw
  rw [← CandidateCapacityValues.capacity_word D s t L B u v]
  exact CandidateCapacityValues.word_width D s t L B _ _

end DirectedFlowCutGap.CandidateCapacityTableData
