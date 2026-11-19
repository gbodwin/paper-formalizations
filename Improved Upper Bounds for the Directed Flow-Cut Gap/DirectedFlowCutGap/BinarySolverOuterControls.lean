import DirectedFlowCutGap.BinaryNaturalOperations
import DirectedFlowCutGap.EncodedEdgeSolver
import DirectedFlowCutGap.BinaryBoundedSampler

/-! Compute the amplification parameters and the draw bound used by the
original input solvers, charging each binary operation. -/
namespace DirectedFlowCutGap.BinarySolverOuterControls

open BinaryNaturalOperations (size_le_self)
open BinaryNaturalOperations (add mul)
open EncodedVertexAmplification (confidenceExponent roundDrawBound)

structure Controls where
  draws : ℕ
  extra : ℕ
  confidence : ℕ
  paid : ℕ

private theorem size_width (n : ℕ) : max 1 n.size=FairBitWords.width n := by
  by_cases h : 0<n
  · rw [BinaryBoundedSampler.size_eq_width h,max_eq_right]
    exact FairBitWords.width_pos n
  · have zero : n=0 := by omega
    subst n
    decide

private def draws (m : ℕ) : ℕ × ℕ :=
  let square := mul m m
  let vertices := mul 4 square.1
  let network := mul 6 vertices.1
  let pair := mul network.1 network.1
  let cube := mul pair.1 network.1
  let repeats := add cube.1 2
  let scan := mul 2 pair.1
  let all := mul repeats.1 scan.1
  (all.1,square.2+vertices.2+network.2+pair.2+cube.2+repeats.2+scan.2+all.2)

private theorem draws_value (m : ℕ) : (draws m).1=roundDrawBound m := by
  simp only [draws,BinaryNaturalOperations.mul_value,BinaryNaturalOperations.add_value,
    roundDrawBound,EncodedUniformRounding.drawBound]
  ring

private def paddedDimension (n width : ℕ) : ℕ × ℕ :=
  let endpoints := mul 2 n
  let layers := add width 3
  let vertices := mul endpoints.1 layers.1
  (vertices.1,endpoints.2+layers.2+vertices.2)

private theorem padded_value (n : ℕ) :
    (paddedDimension n (max 1 n.size)).1=2*n*(Nat.log2 n+4) := by
  simp only [paddedDimension,BinaryNaturalOperations.mul_value,BinaryNaturalOperations.add_value,
    size_width,FairBitWords.width]

private def prepare (n κ : ℕ) (useLine : Bool) : Controls :=
  let count := BinaryNaturalOperations.width n
  let width := max 1 count.1
  let dim := if useLine then paddedDimension n width else (n,0)
  let exponent := mul width κ
  let trials := add exponent.1 1
  let bound := draws dim.1
  ⟨bound.1,exponent.1,trials.1,count.2+dim.2+exponent.2+trials.2+bound.2+12⟩

def vertex (n κ : ℕ) : Controls := prepare n κ false

def edge (n κ : ℕ) : Controls := prepare n κ true

@[simp] theorem vertex_draws (n κ : ℕ) : (vertex n κ).draws=roundDrawBound n := by
  unfold vertex prepare
  dsimp only
  rw [ite_eq_right (by decide : ¬ false = true),draws_value]

@[simp] theorem edge_draws (n κ : ℕ) : (edge n κ).draws=EncodedEdgeSolver.drawBound n := by
  unfold edge prepare
  dsimp only
  rw [ite_eq_left (rfl : true = true),draws_value,BinaryNaturalOperations.width_value,padded_value]
  rfl

private theorem extras (n κ : ℕ) (useLine : Bool) :
    (prepare n κ useLine).extra=confidenceExponent n κ := by
  have changeWidth : max 1 (max 1 n).size = max 1 n.size := by
    by_cases h : 1 ≤ n
    · rw [max_eq_right h]
    · have eq : n=0 := by omega
      subst n
      decide
  simp only [prepare,BinaryNaturalOperations.width_value,BinaryNaturalOperations.mul_value,
    confidenceExponent,← size_width,changeWidth]

@[simp] theorem vertex_extra (n κ : ℕ) : (vertex n κ).extra=confidenceExponent n κ := extras n κ false

@[simp] theorem edge_extra (n κ : ℕ) : (edge n κ).extra=confidenceExponent n κ := extras n κ true

private theorem confidence (n κ : ℕ) (useLine : Bool) :
    (prepare n κ useLine).confidence=confidenceExponent n κ+1 := by
  have same : (prepare n κ useLine).confidence=(prepare n κ useLine).extra+1 := by
    simp only [prepare,BinaryNaturalOperations.add_value]
  exact same.trans (congrArg (·+1) (extras n κ useLine))

@[simp] theorem vertex_confidence (n κ : ℕ) : (vertex n κ).confidence=confidenceExponent n κ+1 :=
  confidence n κ false

@[simp] theorem edge_confidence (n κ : ℕ) : (edge n κ).confidence=confidenceExponent n κ+1 :=
  confidence n κ true

private def paidWidth {R : Type*} [Semiring R] (m : R) : R :=
  let q := 24*(m+1)^2
  q^3+2*q^2+q+m+8

private def drawsBudget {R : Type*} [Semiring R] (m : R) : R :=
  8*(BinaryRawRational.budget (paidWidth m)+4)

private theorem draws_paid (m : ℕ) : (draws m).2 ≤ drawsBudget m := by
  let q := 24*(m+1)^2
  let W := paidWidth m
  let s := mul m m
  let vertices := mul 4 s.1
  let a := mul 6 vertices.1
  let b := mul a.1 a.1
  let c := mul b.1 a.1
  let u := add c.1 2
  let v := mul 2 b.1
  have square : m*m ≤ (m+1)^2 := by rw [pow_two]; gcongr <;> omega
  have verticesValue : vertices.1=4*(m*m) := by simp only [vertices,s,BinaryNaturalOperations.mul_value]
  have asize : a.1 ≤ q := by
    rw [show a.1=6*vertices.1 from BinaryNaturalOperations.mul_value ..,verticesValue]
    unfold q
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left 24 square
  have sSize : s.1 ≤ q := by
    rw [show s.1=m*m from BinaryNaturalOperations.mul_value ..]
    exact square.trans (le_mul_of_one_le_left (Nat.zero_le _) (by decide))
  have vSize : vertices.1 ≤ q := by
    rw [verticesValue]
    exact (Nat.mul_le_mul_left 4 square).trans (Nat.mul_le_mul_right _ (by decide))
  have bSize : b.1 ≤ q^2 := by
    rw [show b.1=a.1*a.1 from BinaryNaturalOperations.mul_value ..,pow_two]
    exact Nat.mul_le_mul asize asize
  have cSize : c.1 ≤ q^3 := by
    rw [show c.1=b.1*a.1 from BinaryNaturalOperations.mul_value ..,pow_succ]
    exact Nat.mul_le_mul bSize asize
  have uSize : u.1 ≤ q^3+2 := by
    rw [show u.1=c.1+2 from BinaryNaturalOperations.add_value ..]
    exact Nat.add_le_add_right cSize _
  have vBound : v.1 ≤ 2*q^2 := by
    rw [show v.1=2*b.1 from BinaryNaturalOperations.mul_value ..]
    exact Nat.mul_le_mul_left _ bSize
  have mBound : m ≤ W := by change m ≤ q^3+2*q^2+q+m+8; omega
  have qBound : q ≤ W := by change q ≤ q^3+2*q^2+q+m+8; omega
  have q2 : q^2 ≤ W := by change q^2 ≤ q^3+2*q^2+q+m+8; omega
  have q3 : q^3+2 ≤ W := by change q^3+2 ≤ q^3+2*q^2+q+m+8; omega
  have pairBound : 2*q^2 ≤ W := by change 2*q^2 ≤ q^3+2*q^2+q+m+8; omega
  have small : ∀ (x : ℕ), x ≤ 6 → x.size ≤ W := by
    intro x h
    apply (size_le_self _).trans
    change x ≤ q^3+2*q^2+q+m+8
    omega
  have sq := BinaryNaturalOperations.mul_paid ((size_le_self _).trans mBound) ((size_le_self _).trans mBound)
  have p2 := BinaryNaturalOperations.mul_paid (small 4 (by decide)) ((size_le_self _).trans (sSize.trans qBound))
  have p3 := BinaryNaturalOperations.mul_paid (small 6 le_rfl) ((size_le_self _).trans (vSize.trans qBound))
  have p4 := BinaryNaturalOperations.mul_paid ((size_le_self _).trans (asize.trans qBound)) ((size_le_self _).trans (asize.trans qBound))
  have p5 := BinaryNaturalOperations.mul_paid ((size_le_self _).trans (bSize.trans q2)) ((size_le_self _).trans (asize.trans qBound))
  have p6 := BinaryNaturalOperations.add_paid ((size_le_self _).trans (cSize.trans (by omega))) (small 2 (by decide))
  have p7 := BinaryNaturalOperations.mul_paid (small 2 (by decide)) ((size_le_self _).trans (bSize.trans q2))
  have p8 := BinaryNaturalOperations.mul_paid ((size_le_self _).trans (uSize.trans q3))
    ((size_le_self _).trans (vBound.trans pairBound))
  change s.2+vertices.2+a.2+b.2+c.2+u.2+v.2+(mul u.1 v.1).2 ≤ 8*(BinaryRawRational.budget W+4)
  change s.2 ≤ _ at sq
  change vertices.2 ≤ _ at p2
  change a.2 ≤ _ at p3
  change b.2 ≤ _ at p4
  change c.2 ≤ _ at p5
  change u.2 ≤ _ at p6
  change v.2 ≤ _ at p7
  omega

private def sizeBound {R : Type*} [Semiring R] (n κ : R) : R :=
  (n+1)*(κ+1)+2*n+κ+n+8

def budget {R : Type*} [Semiring R] (n κ : R) : R :=
  drawsBudget (2*n*(n+4)+n)+5*(BinaryRawRational.budget (sizeBound n κ)+4)+24*(n+1)^2+16

private theorem draws_mono {u v : ℕ} (h : u ≤ v) : drawsBudget u ≤ drawsBudget v := by
  unfold drawsBudget paidWidth BinaryRawRational.budget
  dsimp only
  gcongr

theorem budget_mono {n m κ c : ℕ} (hn : n ≤ m) (hc : κ ≤ c) : budget n κ ≤ budget m c := by
  unfold budget drawsBudget paidWidth BinaryRawRational.budget sizeBound
  dsimp only
  gcongr

open Polynomial in
theorem budget_eval (a b : Polynomial ℕ) (x : ℕ) : (budget a b).eval x=budget (a.eval x) (b.eval x) := by
  simp only [budget,drawsBudget,paidWidth,sizeBound,BinaryRawRational.budget,eval_mul,eval_add,eval_ofNat,eval_pow,eval_one]

private theorem prepare_paid (n κ : ℕ) (useLine : Bool) : (prepare n κ useLine).paid ≤ budget n κ := by
  let W := sizeBound n κ
  let c := BinaryNaturalOperations.width n
  let w := max 1 c.1
  let x := mul w κ
  let y := add x.1 1
  let dim := if useLine then paddedDimension n w else (n,0)
  have wl : w ≤ n+1 := max_le (by omega) ((BinaryNaturalOperations.width_value _).trans_le ((size_le_self _).trans (by omega)))
  have wW : w ≤ W := wl.trans (by unfold W sizeBound; omega)
  have kW : κ ≤ W := by unfold W sizeBound; omega
  have nW : n ≤ W := by unfold W sizeBound; omega
  have oW : 1 ≤ W := by unfold W sizeBound; omega
  have ex : x.1 ≤ (n+1)*κ := (BinaryNaturalOperations.mul_value _ _).trans_le (Nat.mul_le_mul_right _ wl)
  have exW : x.1 ≤ W := by
    apply ex.trans
    have h := Nat.mul_le_mul_left (n+1) (show κ ≤ κ+1 by omega)
    unfold W sizeBound
    omega
  have hcost : c.2 ≤ 24*(n+1)^2+4 := BinaryNaturalOperations.width_paid (size_le_self _)
  have ecost : x.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.mul_paid ((size_le_self _).trans wW) ((size_le_self _).trans kW)
  have ycost : y.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.add_paid ((size_le_self _).trans exW) ((size_le_self _).trans oW)
  have dimMagnitude : dim.1 ≤ 2*n*(n+4)+n := by
    cases useLine
    · change n ≤ _
      omega
    · change (paddedDimension n (max 1 c.1)).1 ≤ _
      rw [show c.1=n.size from BinaryNaturalOperations.width_value _,padded_value]
      exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log2_le_self _) _)).trans (Nat.le_add_right ..)
  have dimCost : dim.2 ≤ 3*(BinaryRawRational.budget W+4) := by
    cases useLine
    · exact Nat.zero_le _
    · let first := mul 2 n
      let second := add w 3
      have h2 : 2 ≤ W := by unfold W sizeBound; omega
      have h3 : 3 ≤ W := by unfold W sizeBound; omega
      have a : first.1 ≤ W := (BinaryNaturalOperations.mul_value ..).trans_le (by unfold W sizeBound; omega)
      have b : second.1 ≤ W := (BinaryNaturalOperations.add_value ..).trans_le (by unfold W sizeBound; omega)
      have pa : first.2 ≤ BinaryRawRational.budget W+4 :=
        BinaryNaturalOperations.mul_paid ((size_le_self 2).trans h2) ((size_le_self _).trans nW)
      have pb : second.2 ≤ BinaryRawRational.budget W+4 :=
        BinaryNaturalOperations.add_paid ((size_le_self _).trans wW) ((size_le_self 3).trans h3)
      have pc := BinaryNaturalOperations.mul_paid ((size_le_self _).trans a) ((size_le_self _).trans b)
      change first.2+second.2+(mul first.1 second.1).2 ≤ _
      omega
  have d := (draws_paid dim.1).trans (draws_mono dimMagnitude)
  change c.2+dim.2+x.2+y.2+(draws dim.1).2+12 ≤ budget n κ
  unfold budget
  change _ ≤ drawsBudget (2*n*(n+4)+n)+5*(BinaryRawRational.budget W+4)+24*(n+1)^2+16
  omega

theorem vertex_paid (n κ : ℕ) : (vertex n κ).paid ≤ budget n κ := prepare_paid n κ false

theorem edge_paid (n κ : ℕ) : (edge n κ).paid ≤ budget n κ := prepare_paid n κ true

attribute [irreducible] vertex edge

end DirectedFlowCutGap.BinarySolverOuterControls
