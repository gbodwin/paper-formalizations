import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.FractionalCoverGraphOracle

/-! Count the binary coordinate comparisons in the actual edge and internal
vertex membership tests on a retained path. -/
namespace DirectedFlowCutGap.MeasuredPathMembership

open BinaryArithmetic (compare_spec)

variable {n : ℕ}

def sameVertex (u v : Fin n) : Bool × ℕ :=
  let a := BinaryNaturalView.encode u.val
  let b := BinaryNaturalView.encode v.val
  let cmp := BinaryArithmetic.compare a.1 b.1
  (cmp.equal,a.2+b.2+cmp.steps)

theorem sameVertex_value (u v : Fin n) : (sameVertex u v).1 = true ↔ u = v := by
  dsimp only [sameVertex]
  rw [(compare_spec _ _).2.1,BinaryNaturalView.encode_value,BinaryNaturalView.encode_value]
  exact ⟨Fin.ext,congrArg Fin.val⟩

def vertexComparisonWork (B : ℕ) : ℕ := 32*(B+1)^2+16*(B+1)

theorem sameVertex_charge (u v : Fin n) {B : ℕ} (a : u.val.size ≤ B) (b : v.val.size ≤ B) :
    (sameVertex u v).2 ≤ vertexComparisonWork B := by
  let x := BinaryNaturalView.encode u.val
  let y := BinaryNaturalView.encode v.val
  have first := (BinaryNaturalView.encode_paid u.val).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right a 1) 2))
  have second := (BinaryNaturalView.encode_paid v.val).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right b 1) 2))
  have sizes : max x.1.length y.1.length ≤ B := by
    apply max_le
    · simpa only [x,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len] using a
    · simpa only [y,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len] using b
  have compare := (compare_spec x.1 y.1).2.2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right sizes 1))
  change x.2 ≤ _ at first
  change y.2 ≤ _ at second
  change x.2+y.2+(BinaryArithmetic.compare x.1 y.1).steps ≤ _
  unfold vertexComparisonWork
  omega

def sameArc (a b : Fin n × Fin n) : Bool × ℕ :=
  let x := sameVertex a.1 b.1
  let y := sameVertex a.2 b.2
  (x.1 && y.1,x.2+y.2+2)

theorem sameArc_value (a b : Fin n × Fin n) : (sameArc a b).1 = true ↔ a = b := by
  simp only [sameArc,Bool.and_eq_true,sameVertex_value,Prod.ext_iff]

def arcComparisonWork (B : ℕ) : ℕ := 2*vertexComparisonWork B+2

theorem sameArc_charge (a b : Fin n × Fin n) :
    (sameArc a b).2 ≤ arcComparisonWork n.size := by
  have first := sameVertex_charge a.1 b.1 (Nat.size_le_size a.1.isLt.le) (Nat.size_le_size b.1.isLt.le)
  have second := sameVertex_charge a.2 b.2 (Nat.size_le_size a.2.isLt.le) (Nat.size_le_size b.2.isLt.le)
  exact (Nat.add_le_add_right (Nat.add_le_add first second) 2).trans_eq (by unfold arcComparisonWork; omega)

def contains {α β : Type*} (equal : α → β → Bool × ℕ) (v : α) : List β → Bool × ℕ
  | [] => (false,1)
  | a::as =>
    let test := equal v a
    if test.1 then (true,test.2+4) else
      let next := contains equal v as
      (next.1,test.2+next.2+4)

theorem contains_value {α β : Type*} (equal : α → β → Bool × ℕ) (key : β → α)
    (v : α) (xs : List β) (correct : ∀ w, (equal v w).1 = true ↔ v = key w) :
    (contains equal v xs).1 = true ↔ v ∈ xs.map key := by
  induction xs with
  | nil => simp [contains]
  | cons x xs ih =>
    by_cases same : v = key x
    · dsimp only [contains]
      rw [ite_eq_left ((correct x).mpr same)]
      simp only [List.map_cons,List.mem_cons,same,true_or]
    · dsimp only [contains]
      rw [ite_eq_right (fun b => same ((correct x).mp b))]
      simpa only [List.map_cons,List.mem_cons,same,false_or] using ih

theorem contains_charge {α β : Type*} (equal : α → β → Bool × ℕ) (v : α) (xs : List β) {B : ℕ}
    (fits : ∀ w ∈ xs, (equal v w).2 ≤ B) :
    (contains equal v xs).2 ≤ xs.length*(B+4)+1 := by
  induction xs with
  | nil => simp [contains]
  | cons a rest ih =>
    have call := fits a List.mem_cons_self
    have tail := ih (fun w member => fits w (List.mem_cons_of_mem _ member))
    dsimp only [contains]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    split
    · omega
    · omega

def arc (e : Fin n × Fin n) (xs : List (Fin n × Fin n)) : Bool × ℕ :=
  contains sameArc e xs

theorem arc_value (e : Fin n × Fin n) (xs : List (Fin n × Fin n)) :
    (arc e xs).1 = true ↔ e ∈ xs := by
  simpa only [arc,List.map_id] using contains_value sameArc id e xs (sameArc_value e)

theorem arc_charge (e : Fin n × Fin n) (xs : List (Fin n × Fin n)) :
    (arc e xs).2 ≤ xs.length*(arcComparisonWork n.size+4)+1 :=
  contains_charge sameArc e xs (fun w _ => sameArc_charge e w)

def internal (v s t : Fin n) (xs : List (Fin n × Fin n)) : Bool × ℕ :=
  let starts := sameVertex v s
  let ends := sameVertex v t
  if starts.1 || ends.1 then (false,starts.2+ends.2+4) else
    let tested := contains (fun u e => sameVertex u e.1) v xs
    (tested.1,starts.2+ends.2+tested.2+4)

theorem internal_value (v s t : Fin n) (xs : List (Fin n × Fin n)) :
    (internal v s t xs).1 = true ↔ v ∈ FractionalCoverGraphOracle.internalColumn s t xs := by
  have found := contains_value (fun u e => sameVertex u e.1) Prod.fst v xs
    (fun e => sameVertex_value v e.1)
  simp only [internal,FractionalCoverGraphOracle.internalColumn,Finset.mem_erase,List.mem_toFinset]
  by_cases endpoint : v = s ∨ v = t
  · have now : ((sameVertex v s).1 || (sameVertex v t).1) = true := by
      simpa only [Bool.or_eq_true,sameVertex_value] using endpoint
    rw [ite_eq_left now]
    rcases endpoint with h | h <;> simp [h]
  · have now : ¬ ((sameVertex v s).1 || (sameVertex v t).1) = true := by
      simpa only [Bool.or_eq_true,sameVertex_value] using endpoint
    rw [ite_eq_right now,found]
    exact ⟨fun listed => ⟨fun h => endpoint (Or.inr h),fun h => endpoint (Or.inl h),listed⟩,
      fun h => h.2.2⟩

def internalWork (B len : ℕ) : ℕ := 2*vertexComparisonWork B+len*(vertexComparisonWork B+4)+5

theorem internal_charge (v s t : Fin n) (xs : List (Fin n × Fin n)) :
    (internal v s t xs).2 ≤ internalWork n.size xs.length := by
  have a := sameVertex_charge v s (Nat.size_le_size v.isLt.le) (Nat.size_le_size s.isLt.le)
  have b := sameVertex_charge v t (Nat.size_le_size v.isLt.le) (Nat.size_le_size t.isLt.le)
  have scan := contains_charge (fun u e => sameVertex u e.1) v xs
    (fun e _ => sameVertex_charge v e.1 (Nat.size_le_size v.isLt.le) (Nat.size_le_size e.1.isLt.le))
  dsimp only [internal,internalWork]
  split <;> omega

end DirectedFlowCutGap.MeasuredPathMembership
