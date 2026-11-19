import DirectedFlowCutGap.BinaryEpochParameters
import DirectedFlowCutGap.BinaryCubeThreshold
import DirectedFlowCutGap.PhysicalIntegerRounding

/-! Execute the integer rounding regime tests on binary words, then call
the same packed controller in the hard regime. -/

namespace DirectedFlowCutGap.BinaryIntegerCutoff

open BinaryArithmetic RetainedGridState
open IntegerEpochParameters (cap fuel)

private def shiftedCap (word : Bits) : Bits := [false,false,false,false,false,false] ++ word

private theorem shiftedCap_value (word : Bits) : value (shiftedCap word)=64*value word := by
  simp only [shiftedCap,List.cons_append,List.nil_append,value,Bool.toNat_false,Nat.zero_add]
  omega

private theorem shiftedCap_length (word : Bits) : (shiftedCap word).length=word.length+6 := by
  simp [shiftedCap,Nat.add_comm]
  omega

private def hardTest (n : Bits) (L : ℕ) (word : Bits) (p : EncodedEpochParameters.Parameters) : Bool × ℕ :=
  let c := BinaryNaturalView.encode p.cap
  let wide := lessEqual (shiftedCap c.1) word
  let cube := BinaryCubeThreshold.test n L
  (wide.1 && cube.1,c.2+wide.2+cube.2+24)

structure Gate where
  parameters : EncodedEpochParameters.Parameters
  inside : Bool
  hard : Bool
  paid : ℕ

def compute (n L : ℕ) : Gate :=
  let p := BinaryEpochParameters.compute n
  let w := BinaryNaturalView.encode n
  let l := BinaryNaturalView.encode L
  let inside := lessEqual l.1 w.1
  let hard := if inside.1 then hardTest w.1 L l.1 p.parameters else (false,4)
  ⟨p.parameters,inside.1,hard.1,p.paid+w.2+l.2+inside.2+hard.2+12⟩

theorem parameters_value (n L : ℕ) : (compute n L).parameters=EncodedEpochParameters.compute n :=
  BinaryEpochParameters.compute_value n

theorem inside_true (n L : ℕ) : (compute n L).inside=true ↔ L≤n := by
  simp only [compute,(lessEqual_spec ..).1,BinaryNaturalView.encode_value]

theorem hard_true (n L : ℕ) (inside : L≤n) :
    (compute n L).hard=true ↔ 64*cap n≤L ∧ n≤L^3 := by
  have yes : (lessEqual (BinaryNaturalView.encode L).1 (BinaryNaturalView.encode n).1).1=true :=
    (inside_true n L).mpr inside
  unfold compute
  dsimp only
  rw [ite_eq_left yes]
  simp only [hardTest,Bool.and_eq_true,(lessEqual_spec ..).1,shiftedCap_value,
    BinaryNaturalView.encode_value,BinaryEpochParameters.compute_value,EncodedEpochParameters.compute_cap,
    BinaryCubeThreshold.test_value,EncodedCubeRootThreshold.cube,pow_succ,pow_zero,Nat.one_mul]

private theorem capSize (n : ℕ) : (BinaryEpochParameters.compute n).parameters.cap.size ≤ 2*n^3+3 := by
  rw [BinaryEpochParameters.compute_value,EncodedEpochParameters.compute_cap,IntegerEpochParameters.cap]
  have h : (4:ℕ)^fuel n=2^(2*fuel n) := by rw [pow_mul]; rfl
  rw [h,Nat.size_pow]
  have f : fuel n ≤ n^3+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  omega

def budget {R : Type*} [Semiring R] (n B : R) : R :=
  BinaryEpochParameters.budget n+16*(n+1)^2+16*(B+1)^2+17*(B+n+1)+
    (16*(2*n^3+4)^2+17*(B+2*n^3+10)+BinaryCubeThreshold.testBudget n+28)+12

set_option maxHeartbeats 1000000 in
theorem compute_paid {n L B : ℕ} (level : L.size ≤ B) : (compute n L).paid ≤ budget n B := by
  let p := BinaryEpochParameters.compute n
  let w := BinaryNaturalView.encode n
  let l := BinaryNaturalView.encode L
  let first := lessEqual l.1 w.1
  let last := hardTest w.1 L l.1 p.parameters
  have work : p.paid ≤ BinaryEpochParameters.budget n := BinaryEpochParameters.compute_paid _
  have wn : w.1.length ≤ n := by
    rw [show w.1=n.bits from BinaryNaturalView.encode_bits n,Nat.size_eq_bits_len]
    exact BinaryNaturalOperations.size_le_self n
  have wl : l.1.length ≤ B := by
    rw [show l.1=L.bits from BinaryNaturalView.encode_bits L,Nat.size_eq_bits_len]
    exact level
  have nw : w.2 ≤ 16*(n+1)^2 := (BinaryNaturalView.encode_paid n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (BinaryNaturalOperations.size_le_self n) 1) 2))
  have lw : l.2 ≤ 16*(B+1)^2 := (BinaryNaturalView.encode_paid L).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right level 1) 2))
  have cmp : first.2 ≤ 17*(B+n+1) := (lessEqual_spec l.1 w.1).2.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (max_le (wl.trans (Nat.le_add_right _ _))
      (wn.trans (Nat.le_add_left _ _))) 1))
  have hard : (if first.1 then last else (false,4)).2 ≤
      16*(2*n^3+4)^2+17*(B+2*n^3+10)+BinaryCubeThreshold.testBudget n+28 := by
    by_cases yes : first.1=true
    · rw [ite_eq_left yes]
      have lim : L≤n := (inside_true n L).mp yes
      let c := BinaryNaturalView.encode p.parameters.cap
      have capWidth := capSize n
      have len : c.1.length ≤ 2*n^3+3 := by
        rw [show c.1=p.parameters.cap.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
        exact capWidth
      have enc := (BinaryNaturalView.encode_paid p.parameters.cap).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right capWidth 1) 2))
      have copy : (shiftedCap c.1).length ≤ 2*n^3+9 := by rw [shiftedCap_length]; omega
      have mx : max (shiftedCap c.1).length l.1.length+1 ≤ B+2*n^3+10 := by
        have hh : max (shiftedCap c.1).length l.1.length ≤ B+2*n^3+9 := max_le (by omega) (by omega)
        omega
      have tail := (lessEqual_spec (shiftedCap c.1) l.1).2.trans (Nat.mul_le_mul_left _ mx)
      have cube := BinaryCubeThreshold.test_paid wn lim
      change c.2 ≤ 16*(2*n^3+4)^2 at enc
      change c.2+(lessEqual (shiftedCap c.1) l.1).2+(BinaryCubeThreshold.test w.1 L).2+24 ≤ _
      omega
    · rw [ite_eq_right yes]
      omega
  change p.paid+w.2+l.2+first.2+(if first.1 then last else (false,4)).2+12 ≤ _
  unfold budget
  omega

theorem budget_mono {n m a b : ℕ} (size : n ≤ m) (width : a ≤ b) : budget n a ≤ budget m b := by
  simp only [budget,BinaryEpochParameters.budget,BinaryEpochParameters.setupWidth,BinaryEpochParameters.logBudget,
    BinaryEpochParameters.logStepBudget,BinaryRawRational.budget,BinaryCubeThreshold.testBudget]
  gcongr

def run {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) :
    Option (PhysicalIntegerRounding.Result n × ℕ) :=
  let gate := compute n L
  let work := gate.parameters.work+2*n+10
  let result : Option (PhysicalIntegerRounding.Result n) := if gate.inside then
    if gate.hard then (PhysicalIntegerRounding.hardRun T adj L tape).map
      (fun result => { result with paid := work+result.paid })
    else some ⟨Vector.replicate n true,tape,work⟩
    else some ⟨Vector.replicate n false,tape,work⟩
  result.map (fun r => (r,gate.paid))

theorem run_cut {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) :
    (run T adj L tape).map Prod.fst=PhysicalIntegerRounding.run T adj L tape := by
  by_cases inside : L≤n
  · have hi := (inside_true n L).mpr inside
    by_cases constraints : 64*cap n≤L ∧ n≤L^3
    · have hh := (hard_true n L inside).mpr constraints
      simp only [run,PhysicalIntegerRounding.run,parameters_value,EncodedEpochParameters.compute_cap,
        ite_eq_left inside,ite_eq_left hi,ite_eq_left constraints,ite_eq_left hh,Option.map_map,Function.comp_def]
    · have hh := fun ran => constraints ((hard_true n L inside).mp ran)
      simp only [run,PhysicalIntegerRounding.run,parameters_value,EncodedEpochParameters.compute_cap,
        ite_eq_left inside,ite_eq_left hi,ite_eq_right constraints,ite_eq_right hh,Option.map_some]
  · have hi := fun ran => inside ((inside_true n L).mp ran)
    simp only [run,PhysicalIntegerRounding.run,parameters_value,ite_eq_right inside,ite_eq_right hi,Option.map_some]

theorem run_paid {n L B : ℕ} (T : ℕ) (adj : PairFlags n) (level : L.size ≤ B)
    (tape : Bits) {r : PhysicalIntegerRounding.Result n × ℕ} (ran : run T adj L tape=some r) :
    r.2 ≤ budget n B := by
  obtain ⟨out,_,rfl⟩ := Option.map_eq_some_iff.mp ran
  exact compute_paid level

end DirectedFlowCutGap.BinaryIntegerCutoff
