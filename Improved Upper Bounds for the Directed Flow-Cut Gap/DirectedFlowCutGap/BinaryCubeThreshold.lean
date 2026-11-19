import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.EncodedCubeRootThreshold

/-! Binary execution of the existing bounded cube-root threshold search. -/

namespace DirectedFlowCutGap.BinaryCubeThreshold

open BinaryArithmetic RawNonnegativeRational

def test (n : Bits) (k : ℕ) : Bool × ℕ :=
  let word := BinaryNaturalView.encode k
  let sq := mulCanonical word.1 word.1
  let cb := mulCanonical sq.1 word.1
  let cmp := lessEqual n cb.1
  (cmp.1,word.2+sq.2+cb.2+cmp.2+8)

theorem test_value (n : Bits) (k : ℕ) : (test n k).1=true ↔ value n ≤ EncodedCubeRootThreshold.cube k := by
  simp only [test,(lessEqual_spec ..).1,(canonical_values ..).2.1,BinaryNaturalView.encode_value,
    EncodedCubeRootThreshold.cube]

def testBudget {R : Type*} [Semiring R] (B : R) : R := 4096*(B+2)^2

theorem test_paid {n : Bits} {k B : ℕ} (width : n.length ≤ B) (index : k ≤ B) : (test n k).2 ≤ testBudget B := by
  let w := BinaryNaturalView.encode k
  let s := mulCanonical w.1 w.1
  let c := mulCanonical s.1 w.1
  have wk : w.1.length ≤ B := by
    rw [show w.1=k.bits from BinaryNaturalView.encode_bits k,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans index
  have large : k ≤ 2^B := (Nat.lt_two_pow_self (n:=k)).le.trans (Nat.pow_le_pow_right (by decide) index)
  have sq : s.1.length ≤ 2*B+1 := by
    change (mulCanonical w.1 w.1).1.length ≤ _
    rw [(canonical_values ..).2.2.2,show value w.1=k from BinaryNaturalView.encode_value k]
    have l : k*k ≤ 2^(2*B) := by rw [two_mul,pow_add]; exact Nat.mul_le_mul large large
    exact (Nat.size_le_size l).trans_eq Nat.size_pow
  have cb : c.1.length ≤ 3*B+1 := by
    change (mulCanonical s.1 w.1).1.length ≤ _
    rw [(canonical_values ..).2.2.2,show value s.1=k*k by
      rw [show value s.1=value w.1*value w.1 from (canonical_values ..).2.1,BinaryNaturalView.encode_value],
      show value w.1=k from BinaryNaturalView.encode_value k]
    have l : k*k*k ≤ 2^(3*B) := by
      rw [show 3*B=B+B+B by omega,pow_add,pow_add]
      exact Nat.mul_le_mul (Nat.mul_le_mul large large) large
    exact (Nat.size_le_size l).trans_eq Nat.size_pow
  have ks : k.size ≤ B := by simpa only [w,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len] using wk
  have encode := (BinaryNaturalView.encode_paid k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ks 1) 2))
  have a := (canonical_charges wk wk).2
  have b := (canonical_charges sq (wk.trans (by omega))).2
  have cmp := (lessEqual_spec n c.1).2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (max_le (width.trans (by omega)) cb) 1))
  change w.2+s.2+c.2+(lessEqual n c.1).2+8 ≤ _
  change w.2 ≤ _ at encode
  change s.2 ≤ _ at a
  change c.2 ≤ _ at b
  unfold testBudget
  nlinarith [Nat.zero_le B]

structure SearchResult where
  root : ℕ
  wordWork : ℕ
  paid : ℕ

def search (n : Bits) : ℕ → ℕ → SearchResult
  | k,0 => ⟨k,1,1⟩
  | k,fuel+1 =>
    let result := test n k
    if result.1 then ⟨k,5,result.2+8⟩ else
      let tail := search n (k+1) fuel
      ⟨tail.root,tail.wordWork+7,tail.paid+result.2+8⟩

theorem search_value (n : Bits) (k fuel : ℕ) :
    ((search n k fuel).root,(search n k fuel).wordWork)=EncodedCubeRootThreshold.search (value n) k fuel := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    have r := test_value n k
    by_cases h : value n ≤ EncodedCubeRootThreshold.cube k
    · simp only [search,EncodedCubeRootThreshold.search,ite_eq_left h,ite_eq_left (r.mpr h)]
    · have no : ¬(test n k).1=true := fun x => h (r.mp x)
      simp only [search,EncodedCubeRootThreshold.search,ite_eq_right h,ite_eq_right no]
      rw [← ih (k+1)]

private theorem search_paid {n : Bits} {k fuel B : ℕ} (width : n.length ≤ B) (indices : k+fuel ≤ B) :
    (search n k fuel).paid ≤ fuel*(testBudget B+8)+1 := by
  induction fuel generalizing k with
  | zero => simp [search]
  | succ fuel ih =>
    have test := test_paid width (show k≤B by omega)
    have next := ih (k:=k+1) (by omega)
    simp only [search,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

structure Result where
  threshold : Code
  wordWork : ℕ
  paid : ℕ

def compute (n : ℕ) : Result :=
  let w := BinaryNaturalView.encode n
  let q := search w.1 1 n
  let code := BinaryNaturalView.encode q.root
  let den := BinaryNaturalView.decode (false::false::code.1)
  ⟨⟨1,den.1,by
      have eq : q.root=EncodedCubeRootThreshold.ceilCube n := by
        have e := congrArg Prod.fst (search_value w.1 1 n)
        rw [show value w.1=n from BinaryNaturalView.encode_value n] at e
        exact e
      rw [BinaryNaturalView.decode_value]
      change 0 < false.toNat+2*(false.toNat+2*value code.1)
      rw [show value code.1=q.root from BinaryNaturalView.encode_value _,eq]
      simp only [Bool.toNat_false,Nat.zero_add]
      exact Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (EncodedCubeRootThreshold.ceilCube_positive n))⟩,
    q.wordWork+7,w.2+q.paid+code.2+den.2+10⟩

theorem compute_value (n : ℕ) : ((compute n).threshold,(compute n).wordWork)=EncodedCubeRootThreshold.thresholdWithCost n := by
  have eq := search_value (BinaryNaturalView.encode n).1 1 n
  rw [BinaryNaturalView.encode_value] at eq
  have e₁ := congrArg Prod.fst eq
  have e₂ := congrArg Prod.snd eq
  dsimp only at e₁ e₂
  simp only [compute,EncodedCubeRootThreshold.thresholdWithCost,BinaryNaturalView.decode_value,value,
    Bool.toNat_false,Nat.zero_add,BinaryNaturalView.encode_value,e₁,e₂]
  have den : 2 * (2 * (EncodedCubeRootThreshold.search n 1 n).1) =
      4 * (EncodedCubeRootThreshold.search n 1 n).1 := by omega
  simp only [den]

def budget {R : Type*} [Semiring R] (n : R) : R := 16*(n+1)^2+n*(testBudget (n+1)+8)+1+
  16*(n+2)^2+16*(n+4)^2+10

theorem compute_paid (n : ℕ) : (compute n).paid ≤ budget n := by
  let w := BinaryNaturalView.encode n
  let q := search w.1 1 n
  let k := BinaryNaturalView.encode q.root
  have h : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have wL : w.1.length ≤ n := by simpa only [w,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len] using h
  have wC : w.2 ≤ 16*(n+1)^2 := (BinaryNaturalView.encode_paid n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2))
  have qu := search_paid (wL.trans (Nat.le_succ n)) (show 1+n≤n+1 by omega)
  have root : q.root ≤ n+1 := by
    have e := congrArg Prod.fst (search_value w.1 1 n)
    rw [show value w.1=n from BinaryNaturalView.encode_value n] at e
    change q.root=EncodedCubeRootThreshold.ceilCube n at e
    rw [e]
    exact EncodedCubeRootThreshold.ceilCube_upper n
  have kSize : q.root.size ≤ n+1 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans root
  have kL : k.1.length ≤ n+1 := by simpa only [k,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len] using kSize
  have kC : k.2 ≤ 16*(n+2)^2 := (BinaryNaturalView.encode_paid q.root).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right kSize 1) 2))
  have dC := (BinaryNaturalView.decode_paid (false::false::k.1)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show (false::false::k.1).length+1≤n+4 by
      simp only [List.length_cons]; omega) 2))
  change q.paid ≤ n*(testBudget (n+1)+8)+1 at qu
  change w.2+q.paid+k.2+(BinaryNaturalView.decode (false::false::k.1)).2+10 ≤ _
  unfold budget
  omega

end DirectedFlowCutGap.BinaryCubeThreshold
