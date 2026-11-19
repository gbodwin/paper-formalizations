import DirectedFlowCutGap.PhysicalBinaryEdgeFamilyCost
import DirectedFlowCutGap.BinaryNaturalOperations

/-! Compute the exact calibrated factor and confidence from the original
stored weight words using measured arithmetic. -/

namespace DirectedFlowCutGap.BinaryEdgeFamilyCalibration

open scoped NNRat ENNReal
open BinaryArithmetic RawNonnegativeRational RandomizedEdgeFamily
open RationalEdgeDecomposition BinaryEdgeFamilyArithmetic
open BinaryNaturalOperations (ofNat_fit size_le_self)

def root (k x : ℕ) : ℕ × ℕ :=
  let width := BinaryNaturalOperations.width x
  let exponent := BinaryNaturalOperations.ceilDiv width.1 k
  let root := BinaryNaturalOperations.powerTwo exponent.1
  (root.1,width.2+exponent.2+root.2+4)

theorem root_value (k x : ℕ) :
    (root k x).1=(EncodedDyadicRoot.powerTwo ((x.size+k-1)/k)).1 := by
  simp only [root,BinaryNaturalOperations.width_value,BinaryNaturalOperations.ceilDiv_value,
    Nat.ceilDiv_eq_add_pred_div,BinaryNaturalOperations.powerTwo_value,EncodedDyadicRoot.powerTwo_value]

theorem exponent_le (x k : ℕ) : x ⌈/⌉ k ≤ x := by
  by_cases h : k=0
  · simp [h]
  · exact (ceilDiv_le_iff_le_mul (Nat.pos_of_ne_zero h)).mpr
      (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right x (show 1 ≤ k from Nat.pos_of_ne_zero h))

theorem root_size (k x : ℕ) : (root k x).1.size ≤ x.size+1 := by
  rw [root_value,EncodedDyadicRoot.powerTwo_value]
  have h := exponent_le x.size k
  rw [Nat.ceilDiv_eq_add_pred_div] at h
  rw [Nat.size_pow]
  exact Nat.add_le_add_right h 1

def rootBudget {R : Type*} [Semiring R] (B : R) : R :=
  24*(B+1)^2+2*BinaryRawRational.budget (2*B)+24*(B+2)^2+16

theorem root_paid {k x B : ℕ} (hk : k.size ≤ B) (hx : x.size ≤ B) : (root k x).2 ≤ rootBudget B := by
  let widths := BinaryNaturalOperations.width x
  let e := BinaryNaturalOperations.ceilDiv widths.1 k
  have size : widths.1 ≤ B := (BinaryNaturalOperations.width_value _).trans_le hx
  have le : e.1 ≤ B := (BinaryNaturalOperations.ceilDiv_value _ _).trans_le ((exponent_le ..).trans size)
  have a := BinaryNaturalOperations.width_paid hx
  have b := BinaryNaturalOperations.ceilDiv_paid ((size_le_self _).trans size) hk
  have c := BinaryNaturalOperations.powerTwo_paid le
  change widths.2 ≤ _ at a
  change e.2 ≤ _ at b
  change widths.2+e.2+(BinaryNaturalOperations.powerTwo e.1).2+4 ≤ _
  unfold rootBudget
  omega

private def ceiling (m : Code) : ℕ × ℕ :=
  let p := BinaryRawRational.mul (Code.ofNat 2) m
  let q := BinaryRawRational.ceil p.1
  let width := BinaryNaturalOperations.width q.1
  (max 1 q.1,p.2+q.2+width.2+16*(width.1+1)^2+4)

theorem ceiling_value (m : Code) : (ceiling m).1=max 1 ⌈2*m.value⌉₊ := by
  simp only [ceiling,BinaryRawRational.ceil_value,Code.ceil_eq,BinaryRawRational.mul_value,Code.value_mul,
    Code.value_ofNat,Nat.cast_ofNat]

private def blank {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Input n := ⟨adj,w,0,0,.mass⟩

private def chooseRoot (a b : ℕ) : (ℕ × CheckedEdgeOracle.Strategy) × ℕ :=
  let cmp := BinaryRawRational.le (Code.ofNat a) (Code.ofNat b)
  (if cmp.1 then (a,.mass) else (b,.size),cmp.2)

private theorem chooseRoot_value (a b : ℕ) :
    (chooseRoot a b).1=if a≤b then (a,.mass) else (b,.size) := by
  simp only [chooseRoot,BinaryRawRational.le_value,Code.le,Code.ofNat,Nat.mul_one,decide_eq_true_eq]

private theorem chooseRoot_size {a b W : ℕ} (ha : a.size ≤ W) (hb : b.size ≤ W) :
    (chooseRoot a b).1.1.size ≤ W := by
  rw [chooseRoot_value]
  split
  · exact ha
  · exact hb

private theorem chooseRoot_paid {a b W : ℕ} (ha : a.size ≤ W) (hb : b.size ≤ W) :
    (chooseRoot a b).2 ≤ BinaryRawRational.budget W :=
  BinaryRawRational.le_paid (ofNat_fit ha) (ofNat_fit hb)

def calibrate {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Input n × ℕ :=
  let a := originals (blank adj w)
  let t := sums a.1 (Vector.replicate (n*n) Code.one)
  let m := t.1.weight
  let control := BinaryEdgeFamilyControls.compute n m
  let boost := BinaryNaturalOperations.width control.horizon
  let conf := BinaryNaturalOperations.add κ boost.1
  let bound := ceiling m
  let g := root k (max 1 n)
  let h := root 2 bound.1
  let s := root 3 (max 1 n)
  let selected := chooseRoot h.1 s.1
  let u := BinaryNaturalOperations.mul M g.1
  let v := BinaryNaturalOperations.mul u.1 selected.1.1
  (⟨adj,w,(v.1 : ℚ≥0),conf.1,selected.1.2⟩,
    a.2+t.2+control.paid+boost.2+conf.2+bound.2+g.2+h.2+s.2+selected.2+u.2+v.2+16*(n+1)^2+20)

theorem calibrate_value {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : (calibrate k M κ adj w).1=calibratedParameters k M κ adj w := by
  let m := (sums (originals (blank adj w)).1 (Vector.replicate (n*n) Code.one)).1.weight
  have value : m.value=originalTotal adj w := by
    simp only [m,sums_weight,originals_value,blank,originalTotal]
  have conf : (BinaryNaturalOperations.add κ
      (BinaryNaturalOperations.width (BinaryEdgeFamilyControls.compute n m).horizon).1).1 =
      κ+(RationalWeakFamily.edgeRounds n (originalTotal adj w)).size := by
    simp only [BinaryNaturalOperations.add_value,BinaryNaturalOperations.width_value,
      BinaryEdgeFamilyControls.compute_horizon,value]
  have bound : (ceiling m).1=massCeiling adj w := by simp only [ceiling_value,value,massCeiling]
  have choices : ((root 2 (ceiling m).1).1≤(root 3 (max 1 n)).1) ↔ preferMass adj w := by
    rw [bound,root_value,root_value]
    rfl
  let mass := (root 2 (ceiling m).1).1
  let size := (root 3 (max 1 n)).1
  let selected := chooseRoot mass size
  have choose : selected.1 = if preferMass adj w then (mass,.mass) else (size,.size) := by
    dsimp only [selected,mass,size]
    simp only [chooseRoot_value,choices]
  change (⟨adj,w,(((BinaryNaturalOperations.mul
      (BinaryNaturalOperations.mul M (root k (max 1 n)).1).1 selected.1.1).1:ℕ):ℚ≥0),
    (BinaryNaturalOperations.add κ (BinaryNaturalOperations.width (BinaryEdgeFamilyControls.compute n m).horizon).1).1,
    selected.1.2⟩ : Input n)=_
  rw [conf,choose,BinaryNaturalOperations.mul_value,BinaryNaturalOperations.mul_value]
  unfold calibratedParameters
  by_cases h : preferMass adj w
  · rw [bestParameters_mass adj w h,ite_eq_left h]
    simp only [mass,bound,root_value]
    rfl
  · rw [bestParameters_size adj w h,ite_eq_right h]
    simp only [size,root_value]
    rfl

def run {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (tape : Bits) : Option (PhysicalBinaryEdgeFamily.Result n) :=
  let params := calibrate k M κ adj w
  (PhysicalBinaryEdgeFamily.run params.1 tape).map
    (fun out => { out with arithmetic := params.2+out.arithmetic })

theorem run_observe {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (tape : Bits) :
    (run k M κ adj w tape).map PhysicalBinaryEdgeFamily.Result.observe =
      (EncodedSolverBits.run (familyTree (calibratedParameters k M κ adj w)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  have ref := PhysicalBinaryEdgeFamily.run_observe (calibratedParameters k M κ adj w) tape
  simp only [run,calibrate_value,Option.map_map,Function.comp_def,PhysicalBinaryEdgeFamily.Result.observe]
  exact ref

private def ceilingBudget {R : Type*} [Semiring R] (B : R) : R :=
  2*BinaryRawRational.budget (B+1)+40*(B+4)^2+8

private theorem ceiling_fits_paid {m : Code} {B : ℕ} (h : m.Bounded B) :
    (ceiling m).1.size ≤ B+3 ∧ (ceiling m).2 ≤ ceilingBudget B := by
  let p := BinaryRawRational.mul (Code.ofNat 2) m
  let q := BinaryRawRational.ceil p.1
  let w := BinaryNaturalOperations.width q.1
  have two : (Code.ofNat 2).Bounded 1 := ⟨by decide,by decide⟩
  have fields : p.1.Bounded (B+1) := by
    change (BinaryRawRational.mul (Code.ofNat 2) m).1.Bounded _
    rw [BinaryRawRational.mul_value]
    simpa only [Nat.add_comm] using Code.bounded_mul two h
  have size : q.1.size ≤ B+3 := by
    change (BinaryRawRational.ceil p.1).1.size ≤ _
    rw [BinaryRawRational.ceil_value]
    exact (Nat.size_le_size (((Nat.div_le_self ..).trans (Nat.sub_le ..)).trans
      (Code.ceiling_intermediate fields))).trans_eq Nat.size_pow
  constructor
  · change (max 1 q.1).size ≤ _
    by_cases hi : 1 ≤ q.1
    · rw [max_eq_right hi]
      exact size
    · rw [max_eq_left (by omega : q.1 ≤ 1)]
      exact (show (1 : ℕ).size = 1 by decide).trans_le (by omega)
  · have a : p.2 ≤ BinaryRawRational.budget (B+1) := BinaryRawRational.mul_paid
      (Code.bounded_mono two (by omega : 1 ≤ B+1)) (Code.bounded_mono h (Nat.le_succ _))
    have b := BinaryRawRational.ceil_paid fields
    change q.2 ≤ BinaryRawRational.budget (B+1) at b
    have c := BinaryNaturalOperations.width_paid size
    have wi : w.1 ≤ B+3 := (BinaryNaturalOperations.width_value _).trans_le size
    have d := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (show w.1+1 ≤ B+4 by omega) 2)
    change w.2 ≤ 24*(B+4)^2+4 at c
    change p.2+q.2+w.2+16*(w.1+1)^2+4 ≤ _
    unfold ceilingBudget
    omega

open PhysicalBinaryEdgeFamilyCost (horizonBound)

def calibrationWidth {R : Type*} [Semiring R] (n B k M κ : R) : R :=
  n*n*(B+1)+n+k+M+κ+horizonBound n B+10

def budget {R : Type*} [Semiring R] (n B k M κ : R) : R :=
  let W := calibrationWidth n B k M κ
  n*n*(40*(B+1)^2)+8*(n*n)+4+sumBudget n B+
  BinaryEdgeFamilyControls.budget n (n*n*(B+1))+(24*(W+1)^2+4)+(BinaryRawRational.budget W+4)+
  ceilingBudget (n*n*(B+1))+3*rootBudget W+3*(BinaryRawRational.budget (2*W+2)+4)+16*(n+1)^2+20

set_option maxHeartbeats 1500000 in
theorem calibrate_paid {n B : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (fit : AdaptiveWidthEnvelope.StoredWeights w B) :
    (calibrate k M κ adj w).2 ≤ budget n B k M κ := by
  let D := blank adj w
  let a := originals D
  let t := sums a.1 (Vector.replicate (n*n) Code.one)
  let m := t.1.weight
  let c := BinaryEdgeFamilyControls.compute n m
  let boost := BinaryNaturalOperations.width c.horizon
  let conf := BinaryNaturalOperations.add κ boost.1
  let massCap := ceiling m
  let g := root k (max 1 n)
  let h := root 2 massCap.1
  let s := root 3 (max 1 n)
  let selected := chooseRoot h.1 s.1
  let chosen := selected.1.1
  let u := BinaryNaturalOperations.mul M g.1
  let v := BinaryNaturalOperations.mul u.1 chosen
  let L := n*n*(B+1)
  let H := horizonBound n B
  let W := calibrationWidth n B k M κ
  have expanded : W=L+n+k+M+κ+H+10 := rfl
  have widths : Fits a.1 B := originals_width D fit
  have unit : Fits (Vector.replicate (n*n) Code.one) B := fun _ => by
    simpa only [Vector.getElem_replicate] using Code.bounded_mono Code.bounded_one (Nat.zero_le B)
  have massFit : m.Bounded L := (sums_bounds a.1 _ widths unit).1
  have horizon : c.horizon ≤ H := by
    have hvalue : m.value=originalTotal D.adjacency D.weights := by simp only [m,t,sums_weight,originals_value,a,originalTotal]
    have ev := (BinaryEdgeFamilyControls.compute_horizon n m).trans
      (congrArg (RationalWeakFamily.edgeRounds n) hvalue)
    have fitD : InputFits D B := ⟨NNRatStoredBounds.mono NNRatStoredBounds.zero_bounded (Nat.zero_le _),fit⟩
    exact ev.trans_le (rounds_le D fitD)
  have boostSize : c.horizon.size ≤ W := (size_le_self _).trans (horizon.trans (by omega))
  have boostOut : boost.1.size ≤ W := (size_le_self _).trans
    ((BinaryNaturalOperations.width_value _).trans_le boostSize)
  have confWidth : κ.size ≤ W := (size_le_self _).trans (by omega)
  have kWidth : k.size ≤ W := (size_le_self _).trans (by omega)
  have mWidth : M.size ≤ W := (size_le_self _).trans (by omega)
  have dim : (max 1 n).size ≤ W := (size_le_self _).trans (max_le (by omega) (by omega))
  have two : (2 : ℕ).size ≤ W := (show (2 : ℕ).size=2 by decide).trans_le (by omega)
  obtain ⟨massSize,massPaid⟩ : massCap.1.size ≤ L+3 ∧ massCap.2 ≤ ceilingBudget L := ceiling_fits_paid massFit
  have rootSize : massCap.1.size ≤ W := massSize.trans (by omega)
  have gs : g.1.size ≤ W+1 := (root_size _ _).trans (Nat.add_le_add_right dim _)
  have hs : h.1.size ≤ W+1 := (root_size _ _).trans (Nat.add_le_add_right rootSize _)
  have ss : s.1.size ≤ W+1 := (root_size _ _).trans (Nat.add_le_add_right dim _)
  have both : chosen.size ≤ W+1 := chooseRoot_size hs ss
  have us : u.1.size ≤ 2*W+2 := by
    change (BinaryNaturalOperations.mul M g.1).1.size ≤ _
    rw [BinaryNaturalOperations.mul_value]
    have h1 := Nat.lt_size_self M
    have h2 := Nat.lt_size_self g.1
    have power : M*g.1 ≤ 2^(M.size+g.1.size) := by rw [pow_add]; exact Nat.mul_le_mul h1.le h2.le
    exact ((Nat.size_le_size power).trans_eq Nat.size_pow).trans (by omega)
  let F := 2*W+2
  have aPaid : a.2 ≤ n*n*(40*(B+1)^2)+8*(n*n)+4 := originals_paid D fit
  have tPaid : t.2 ≤ sumBudget n B := sums_paid a.1 _ widths unit
  have cPaid : c.paid ≤ BinaryEdgeFamilyControls.budget n L := BinaryEdgeFamilyControls.compute_paid _ massFit
  have wPaid : boost.2 ≤ 24*(W+1)^2+4 := BinaryNaturalOperations.width_paid boostSize
  have confPaid : conf.2 ≤ BinaryRawRational.budget W+4 := BinaryNaturalOperations.add_paid confWidth boostOut
  have gPaid : g.2 ≤ rootBudget W := root_paid kWidth dim
  have hPaid : h.2 ≤ rootBudget W := root_paid two rootSize
  have three : (3:ℕ).size ≤ W := (show (3:ℕ).size=2 by decide).trans_le (by omega)
  have sPaid : s.2 ≤ rootBudget W := root_paid three dim
  have cmpPaid : selected.2 ≤ BinaryRawRational.budget F :=
    chooseRoot_paid (hs.trans (by unfold F; omega)) (ss.trans (by unfold F; omega))
  have uPaid : u.2 ≤ BinaryRawRational.budget F+4 :=
    BinaryNaturalOperations.mul_paid (mWidth.trans (by unfold F; omega)) (gs.trans (by unfold F; omega))
  have vPaid : v.2 ≤ BinaryRawRational.budget F+4 :=
    BinaryNaturalOperations.mul_paid us (both.trans (by unfold F; omega))
  change a.2+t.2+c.paid+boost.2+conf.2+massCap.2+g.2+h.2+s.2+selected.2+u.2+v.2+16*(n+1)^2+20 ≤
    n*n*(40*(B+1)^2)+8*(n*n)+4+sumBudget n B+BinaryEdgeFamilyControls.budget n L+(24*(W+1)^2+4)+
    (BinaryRawRational.budget W+4)+ceilingBudget L+3*rootBudget W+3*(BinaryRawRational.budget F+4)+16*(n+1)^2+20
  omega

open Polynomial
open PhysicalIntegerRoundingCost (eval_mono)

theorem budget_eval (n b k M κ : Polynomial ℕ) (x : ℕ) :
    (budget n b k M κ).eval x=budget (n.eval x) (b.eval x) (k.eval x) (M.eval x) (κ.eval x) := by
  simp only [budget,calibrationWidth,horizonBound,sumBudget,BinaryEdgeFamilyControls.budget,ceilingBudget,rootBudget,
    BinaryRawRational.budget,BinaryVertexReductionArithmetic.aggregateWidth,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

theorem budget_mono {n m b B k M c C : ℕ} (hn : n ≤ m) (hb : b ≤ B) (hc : c ≤ C) :
    budget n b k M c ≤ budget m B k M C := by
  simp only [budget,calibrationWidth,horizonBound,sumBudget,BinaryEdgeFamilyControls.budget,ceilingBudget,rootBudget,
    BinaryRawRational.budget,BinaryVertexReductionArithmetic.aggregateWidth]
  gcongr

theorem run_polynomial {k : ℕ} (positive : 0<k) (M : ℕ) :
    ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
      (w : RationalEdgeThresholds.Weights n) (_fit : AdaptiveWidthEnvelope.StoredWeights w B)
      (tape : Bits) {r : PhysicalBinaryEdgeFamily.Result n}, run k M κ adj w tape=some r →
      r.total ≤ p.eval (n+B+κ) := by
  obtain ⟨p,hp⟩ := PhysicalBinaryEdgeFamilyCost.calibrated_polynomial positive M
  refine ⟨p+budget X X (C k) (C M) X,?_⟩
  intro n B κ adj w fit tape r ran
  let x := n+B+κ
  let params := calibrate k M κ adj w
  change (PhysicalBinaryEdgeFamily.run params.1 tape).map (fun out =>
    { out with arithmetic := params.2+out.arithmetic })=some r at ran
  obtain ⟨out,actual,rfl⟩ := Option.map_eq_some_iff.mp ran
  rw [show params.1=calibratedParameters k M κ adj w from calibrate_value ..] at actual
  have lower := hp κ adj w fit tape actual
  change out.total ≤ p.eval x at lower
  have setup := (calibrate_paid k M κ adj w fit).trans (budget_mono
    (show n ≤ x by unfold x; omega) (show B ≤ x by unfold x; omega) (show κ ≤ x by unfold x; omega))
  rw [eval_add,budget_eval,eval_X,eval_C,eval_C]
  change out.dispatch+out.readback+out.roundingAndSelection+(params.2+out.arithmetic) ≤ p.eval x+budget x x k M x
  change params.2 ≤ _ at setup
  unfold PhysicalBinaryEdgeFamily.Result.total at lower
  omega

/-- The calibrated entry computes its parameters and adaptive queries, and
returns the original-weight guarantee and a polynomial for its recorded work. -/
theorem calibrated_verified (ε : ℝ) (positive : 0<ε) :
    ∃ k M : ℕ, ∃ p : Polynomial ℕ, 0<k ∧ 0<M ∧
      ∀ (n : ℕ), 2≤n → ∀ (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (B κ : ℕ), AdaptiveWidthEnvelope.StoredWeights w B →
        let D := calibratedParameters k M κ adj w
        let bits := readBudget n (inputWidth D) D.confidence
        ((EncodedSolverBits.fairTape bits).map (fun tape => ((run k M κ adj w tape).map (fun r => r.observe.1)).join)) none ≤
          ENNReal.ofReal ((n : ℝ)^(-(κ : ℝ))) ∧
        ∀ tape : Bits, bits≤tape.length →
          ∃ out used, run k M κ adj w tape=some out ∧ out.suffix=tape.drop used ∧ used≤bits ∧
            out.total ≤ p.eval (n+B+κ) ∧
            ∀ s, out.history=some s → s.cuts.length=rounds D ∧ (∀ X∈s.cuts, Good adj w X) ∧
              ∀ e, (CheckedMWHistory.occurrences s.observe e : ℝ)/(s.cuts.length : ℝ) ≤
                8*(originalWeight adj w e : ℝ)*(8*(M : ℝ)*(n : ℝ)^ε*(originalTotal adj w : ℝ)^(1/2 : ℝ)) := by
  obtain ⟨k,M,hk,hM,law⟩ := calibrated_families ε positive
  obtain ⟨p,pay⟩ := run_polynomial hk M
  refine ⟨k,M,p,hk,hM,?_⟩
  intro n large adj w B κ fit
  dsimp only
  let D := calibratedParameters k M κ adj w
  obtain ⟨chance,complete⟩ := law n large adj w κ
  constructor
  · have eq : (fun tape => ((run k M κ adj w tape).map (fun r => r.observe.1)).join) =
        (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join) := by
      funext tape
      have h := congrArg (fun r => (r.map Prod.fst).join) (run_observe k M κ adj w tape)
      simpa only [Option.map_map,Function.comp_def] using h
    rw [eq]
    exact chance
  · intro tape enough
    obtain ⟨hist,used,exactRun,bound,good⟩ := complete tape enough
    have law := run_observe k M κ adj w tape
    rw [exactRun] at law
    cases actual : run k M κ adj w tape with
    | none => simp [actual] at law
    | some out =>
      have equal : out.observe=(hist,tape.drop used) :=
        by simpa only [actual,Option.map_some,Option.some.injEq] using law
      refine ⟨out,used,rfl,congrArg Prod.snd equal,bound,pay κ adj w fit tape actual,?_⟩
      intro s selected
      have history : out.history.map BinaryEdgeFamilyState.State.observe=hist := congrArg Prod.fst equal
      rw [selected,Option.map_some] at history
      exact good s.observe history.symm

end DirectedFlowCutGap.BinaryEdgeFamilyCalibration
