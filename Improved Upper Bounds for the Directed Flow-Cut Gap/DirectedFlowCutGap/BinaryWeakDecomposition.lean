import DirectedFlowCutGap.BinaryEdgeFamilyCalibration
import DirectedFlowCutGap.BinaryFamilySampler

/-! Use the unread tape of the calibrated edge family to select a cut.
Rejection stays visible as failure, so it does not add to any edge marginal. -/
namespace DirectedFlowCutGap.BinaryWeakDecomposition

open scoped ENNReal
open BinaryArithmetic FiniteDrawTrees RandomizedEdgeFamily RationalEdgeDecomposition
open RationalWeakFamily (History)
open FiniteAmplification (probability)

private abbrev Cut (n : ℕ) := Finset (Edge n)

def samplingControl (n κ : ℕ) : ℕ × ℕ × ℕ :=
  let next := BinaryNaturalOperations.add κ 1
  let size := BinaryNaturalOperations.width n
  let exponent := BinaryNaturalOperations.mul (max 1 size.1) next.1
  (next.1,exponent.1,next.2+size.2+exponent.2+8)

private theorem controls_eq (n κ : ℕ) :
    (samplingControl n κ).1=κ+1 ∧
      (samplingControl n κ).2.1=EncodedVertexAmplification.confidenceExponent n (κ+1) := by
  have size : max 1 n.size=FairBitWords.width (max 1 n) := by
    cases n with
    | zero => decide
    | succ n =>
      have h : 0<n+1 := Nat.succ_pos _
      have one : 1 ≤ (n+1).size := by
        exact (Nat.pos_of_ne_zero (fun zero => h.ne' (Nat.size_eq_zero.mp zero)))
      rw [max_eq_right one,max_eq_right h,BinaryBoundedSampler.size_eq_width h]
  simp only [samplingControl,BinaryNaturalOperations.add_value,BinaryNaturalOperations.width_value,
    BinaryNaturalOperations.mul_value,EncodedVertexAmplification.confidenceExponent,size,and_self]

private def select {A : Type} (T : ℕ) : Option (List A) → FiniteDrawTrees.Tree (Option A × ℕ)
  | none => .pure (none,0)
  | some cuts => BinaryFamilySampler.choose cuts T

private def next {n : ℕ} (T : ℕ) (s : Option (History (Edge n))) : FiniteDrawTrees.Tree (Option (Cut n) × ℕ) :=
  select T (s.map History.cuts)

def tree {n : ℕ} (D : Input n) (T : ℕ) : FiniteDrawTrees.Tree (Option (Cut n) × ℕ) :=
  FiniteDrawTrees.bind (familyTree D) (next T)

structure Result (n : ℕ) where
  cut : Option (Cut n)
  suffix : Bits
  familyPaid : ℕ
  samplePaid : ℕ

def Result.observe {n : ℕ} (r : Result n) : (Option (Cut n) × ℕ) × Bits :=
  ((r.cut,r.samplePaid),r.suffix)

def run {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (tape : Bits) : Option (Result n) :=
  let controls := samplingControl n κ
  (BinaryEdgeFamilyCalibration.run k M controls.1 adj w tape).bind fun family =>
    (EncodedSolverBits.run (select controls.2.1 (family.history.map BinaryEdgeFamilyState.State.cuts))
      family.suffix).map fun ((cut,paid),(rest,_)) =>
        ⟨cut,rest,family.total+controls.2.2,paid⟩

attribute [local irreducible] BinaryEdgeFamilyCalibration.run

theorem run_observe {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (tape : Bits) :
    let D := calibratedParameters k M (κ+1) adj w
    let T := EncodedVertexAmplification.confidenceExponent n (κ+1)
    (run k M κ adj w tape).map Result.observe =
      (EncodedSolverBits.run (tree D T) tape).map (fun (out,(rest,_)) => (out,rest)) := by
  dsimp only
  change _ = (EncodedSolverBits.run ((familyTree _) >>= next _) tape).map _
  rw [EncodedSolverBits.run_bind_observe,← BinaryEdgeFamilyCalibration.run_observe]
  unfold run
  dsimp only
  rw [(controls_eq n κ).1,(controls_eq n κ).2]
  cases family : BinaryEdgeFamilyCalibration.run k M (κ+1) adj w tape with
  | none => rfl
  | some out =>
    have lists : (out.observe.1.map History.cuts)=out.history.map BinaryEdgeFamilyState.State.cuts := by
      simp only [PhysicalBinaryEdgeFamily.Result.observe,Option.map_map,Function.comp_def,BinaryEdgeFamilyState.State.observe]
    have suffix : out.observe.2=out.suffix := rfl
    simp only [Option.map_some,Option.bind_some,next,lists,suffix]
    cases EncodedSolverBits.run
      (select (EncodedVertexAmplification.confidenceExponent n (κ+1))
        (out.history.map BinaryEdgeFamilyState.State.cuts)) out.suffix <;> rfl

private theorem within_bind_support {A B : Type} {p : FiniteDrawTrees.Tree A} {q r : ℕ}
    (h : Within q p) (f : A → FiniteDrawTrees.Tree B) (hf : ∀ a ∈ (ideal p).support, Within r (f a)) :
    Within (q+r) (FiniteDrawTrees.bind p f) := by
  induction h with
  | pure q a =>
    have hit : a ∈ (ideal (.pure a)).support := by simp [ideal,law]
    exact within_mono (hf a hit) (Nat.le_add_left _ _)
  | @draw q n pos rest children ih =>
    let : NeZero n := ⟨pos.ne'⟩
    have lift (j : Fin n) (a : A) (ha : a ∈ (ideal (rest j)).support) :
        a ∈ (ideal (.draw n pos rest)).support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨j,PMF.mem_support_uniformOfFintype _,ha⟩
    have branches (j : Fin n) : Within (q+r) (FiniteDrawTrees.bind (rest j) f) := ih j (fun a ha => hf a (lift j a ha))
    simpa only [FiniteDrawTrees.bind,Nat.add_assoc,Nat.add_comm 1 r] using
      (Within.draw branches : Within (q+r+1) (.draw n pos (fun j => FiniteDrawTrees.bind (rest j) f)))

theorem tree_within {n B : ℕ} (hn : 0<n) (D : Input n) (hα : 1≤D.factor) (fit : InputFits D B)
    (T : ℕ) (lengths : ∀ s, some s ∈ (ideal (familyTree D)).support → s.cuts.length=rounds D) :
    Within (readBudget n B D.confidence+T*FairBitWords.width (rounds D)) (tree D T) := by
  apply within_bind_support (familyTree_within hn D hα fit) (next T)
  intro s hit
  cases s with
  | none => exact .pure _ _
  | some hist =>
    rw [← lengths hist hit]
    exact BinaryFamilySampler.choose_within hist.cuts T

theorem tree_binary {n : ℕ} (D : Input n) (T : ℕ) : LazyFairBitTrees.Binary (tree D T) := by
  apply LazyFairBitTrees.binary_bind (familyTree_binary D) (next T)
  intro s
  cases s with
  | none => exact .pure _
  | some hist => exact BinaryFamilySampler.choose_binary hist.cuts T

private theorem run_law {A : Type} {q : ℕ} {t : FiniteDrawTrees.Tree (Option A × ℕ)}
    (within : Within q t) (binary : LazyFairBitTrees.Binary t) :
    (EncodedSolverBits.fairTape q).map (fun tape => ((EncodedSolverBits.run t tape).map (fun out => out.1.1)).join)
      = (ideal t).map Prod.fst := by
  have h := congrArg (PMF.map (fun (o : Option (Option A × ℕ)) => (o.map Prod.fst).join))
    (EncodedSolverBits.run_fairTape within binary)
  simpa only [PMF.map_comp,Function.comp_def,Option.map_map,Option.map_some,Option.join_some] using h

private theorem family_law {A : Type} {q : ℕ} {t : FiniteDrawTrees.Tree (Option A)}
    (within : Within q t) (binary : LazyFairBitTrees.Binary t) :
    (EncodedSolverBits.fairTape q).map (fun bs => ((EncodedSolverBits.run t bs).map Prod.fst).join) = ideal t := by
  have h := congrArg (PMF.map Option.join) (EncodedSolverBits.run_fairTape within binary)
  simp only [PMF.map_comp,Function.comp_def,Option.join_some] at h
  exact h.trans (PMF.map_id (ideal t))

theorem fair_law {n : ℕ} (k M κ q : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n)
    (within : Within q (tree (calibratedParameters k M (κ+1) adj w)
      (EncodedVertexAmplification.confidenceExponent n (κ+1)))) :
    (EncodedSolverBits.fairTape q).map (fun tape => ((run k M κ adj w tape).map Result.cut).join) =
      (ideal (tree (calibratedParameters k M (κ+1) adj w)
          (EncodedVertexAmplification.confidenceExponent n (κ+1)))).map Prod.fst := by
  rw [← run_law within (tree_binary ..)]
  apply congrArg (fun f => (EncodedSolverBits.fairTape q).map f)
  funext tape
  have h := congrArg (fun o => (o.map (fun r => r.1.1)).join) (run_observe k M κ adj w tape)
  simpa only [Option.map_map,Function.comp_def,Result.observe] using h


private theorem law_tree {n : ℕ} (D : Input n) (T : ℕ) :
    (ideal (tree D T)).map Prod.fst =
      (ideal (familyTree D)).bind (fun s => (ideal (next T s)).map Prod.fst) := by
  have e := law_bind uniformDraw (familyTree D) (next T)
  change ideal (tree D T)=_ at e
  rw [e,PMF.map_bind]

private theorem rounds_pos {n : ℕ} (D : Input n) : 0<rounds D :=
  RationalWeakFamily.edgeRounds_pos ..

theorem law_valid {n : ℕ} (D : Input n) (T : ℕ)
    (valid : ∀ s, some s ∈ (ideal (familyTree D)).support → ∀ X ∈ s.cuts, Good D.adjacency D.weights X) :
    ∀ X, some X ∈ ((ideal (tree D T)).map Prod.fst).support → Good D.adjacency D.weights X := by
  intro X hit
  rw [law_tree] at hit
  obtain ⟨s,seen,picked⟩ := (PMF.mem_support_bind_iff _ _ _).mp hit
  cases s with
  | none => simp [next,select,law] at picked
  | some hist =>
    change some X ∈ ((ideal (BinaryFamilySampler.choose hist.cuts T)).map Prod.fst).support at picked
    obtain ⟨r,hr,hcut⟩ := (PMF.mem_support_map_iff _ _ _).mp picked
    apply valid hist seen X
    exact (BinaryFamilySampler.choose_supported hist.cuts T hr).1 X (hcut ▸ (Option.mem_some_iff.mpr rfl))

theorem law_failure {n : ℕ} (D : Input n) (T : ℕ)
    (lengths : ∀ s, some s ∈ (ideal (familyTree D)).support → s.cuts.length=rounds D) :
    ((ideal (tree D T)).map Prod.fst) none ≤
      (ideal (familyTree D)) none + ENNReal.ofReal (((1:ℝ)/2)^T) := by
  classical
  let p := ideal (familyTree D)
  let q := ENNReal.ofReal (((1:ℝ)/2)^T)
  rw [law_tree,PMF.bind_apply]
  change (∑' s, p s*((ideal (next T s)).map Prod.fst) none) ≤ p none+q
  have point (s : Option (History (Edge n))) :
      p s*((ideal (next T s)).map Prod.fst) none ≤ (if s=none then p s else 0)+p s*q := by
    by_cases hs : s ∈ p.support
    · cases s with
      | none =>
        rw [show (ideal (next T (none : Option (History (Edge n))))).map Prod.fst=PMF.pure none from
          PMF.pure_map Prod.fst (none,0),PMF.pure_apply_self]
        simp
      | some hist =>
        have pos : 0<hist.cuts.length := (lengths hist hs).symm ▸ rounds_pos D
        have h := ENNReal.ofReal_le_ofReal (BoundedBitRejection.law_failure_le pos T)
        rw [ENNReal.ofReal_toReal ((BoundedBitRejection.law hist.cuts.length T).apply_ne_top none)] at h
        simp only [next,Option.map_some,select,BinaryFamilySampler.choose_failure _ pos,reduceCtorEq,
          ite_false,zero_add]
        exact mul_le_mul_of_nonneg_left h zero_le
    · have hz : p s=0 := by simpa only [PMF.mem_support_iff,not_ne_iff] using hs
      rw [hz,zero_mul,zero_mul,ite_self,add_zero]
  apply (ENNReal.tsum_le_tsum point).trans
  rw [ENNReal.tsum_add,ENNReal.tsum_mul_right,p.tsum_coe,one_mul]
  simp

private theorem sampler_marginal {A : Type} [Fintype A] (xs : List A) (pos : 0<xs.length) (T : ℕ)
    (P : A → Prop) [DecidablePred P] (L : ℝ)
    (freq : (xs.countP (fun a => decide (P a)) : ℝ)/(xs.length : ℝ) ≤ L) :
    let p := (ideal (BinaryFamilySampler.choose xs T)).map Prod.fst
    probability p (fun o => ∃ a ∈ o, P a) ≤ L * probability p (fun o => o.isSome) := by
  dsimp only
  have success := BinaryFamilySampler.choose_marginal xs pos T (fun _ => True)
  have equiv : (fun o : Option A => ∃ a ∈ o, True) = (fun o => (o.isSome : Prop)) := by
    funext o
    apply propext
    cases o <;> simp
  rw [equiv] at success
  have nonempty : (xs.length : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  simp only [decide_true,List.countP_true,div_self nonempty,mul_one] at success
  rw [BinaryFamilySampler.choose_marginal xs pos,success]
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    ((BoundedBitRejection.law xs.length T).coe_le_one none)
  rw [ENNReal.toReal_one] at h
  exact (mul_le_mul_of_nonneg_left freq (sub_nonneg.mpr h)).trans_eq (mul_comm _ _)

private theorem mass_finite {A : Type} (p : PMF A) (E : Set A) : p.toOuterMeasure E ≠ ∞ := by
  rw [PMF.toOuterMeasure_apply]
  exact p.tsum_coe_indicator_ne_top E

/-- The deletion bound survives conditioning on a returned cut. -/
theorem law_marginal {n : ℕ} (D : Input n) (T : ℕ) (e : Edge n) (L : ℝ) (nonneg : 0≤L)
    (lengths : ∀ s, some s ∈ (ideal (familyTree D)).support → s.cuts.length=rounds D)
    (freq : ∀ s, some s ∈ (ideal (familyTree D)).support →
      (CheckedMWHistory.occurrences s e : ℝ)/(s.cuts.length : ℝ) ≤ L) :
    let p := (ideal (tree D T)).map Prod.fst
    probability p (fun o => ∃ X ∈ o, e ∈ X) ≤ L * probability p (fun o => o.isSome) := by
  dsimp only
  let p := ideal (familyTree D)
  let f := fun s : Option (History (Edge n)) => (ideal (next T s)).map Prod.fst
  let E : Set (Option (Cut n)) := {o | ∃ X ∈ o, e ∈ X}
  let S : Set (Option (Cut n)) := {o | o.isSome}
  have point (s : Option (History (Edge n))) :
      p s*(f s).toOuterMeasure E ≤ p s*(ENNReal.ofReal L*(f s).toOuterMeasure S) := by
    by_cases hs : s ∈ p.support
    · cases s with
      | none =>
        rw [show f none=PMF.pure none from PMF.pure_map Prod.fst (none,0)]
        rw [PMF.toOuterMeasure_pure_apply]
        simp [E]
      | some hist =>
        let law := (ideal (BinaryFamilySampler.choose hist.cuts T)).map Prod.fst
        have pos : 0<hist.cuts.length := (lengths hist hs).symm ▸ rounds_pos D
        have hb := sampler_marginal hist.cuts pos T (fun X => e ∈ X) L (freq hist hs)
        have le : law.toOuterMeasure E ≤ ENNReal.ofReal L * law.toOuterMeasure S := by
          rw [← ENNReal.ofReal_toReal (mass_finite law E),← ENNReal.ofReal_toReal (mass_finite law S),
            ← ENNReal.ofReal_mul nonneg]
          exact ENNReal.ofReal_le_ofReal hb
        exact mul_le_mul_of_nonneg_left le zero_le
    · have hz : p s=0 := by simpa only [PMF.mem_support_iff,not_ne_iff] using hs
      rw [hz,zero_mul,zero_mul]
  have h := ENNReal.tsum_le_tsum point
  simp_rw [mul_left_comm (p _) (ENNReal.ofReal L)] at h
  rw [ENNReal.tsum_mul_left,← PMF.toOuterMeasure_bind_apply,← PMF.toOuterMeasure_bind_apply] at h
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (mass_finite (p.bind f) S)) h
  simpa only [probability,law_tree,ENNReal.toReal_mul,ENNReal.toReal_ofReal nonneg] using ht

private theorem tape_length {q : ℕ} {tape : Bits} (h : tape ∈ (EncodedSolverBits.fairTape q).support) :
    tape.length=q := by
  induction q generalizing tape with
  | zero =>
    have eq : tape=[] := by simpa only [EncodedSolverBits.fairTape,PMF.support_pure,Set.mem_singleton_iff] using h
    rw [eq]
    rfl
  | succ q ih =>
    unfold EncodedSolverBits.fairTape at h
    obtain ⟨i,_,pushed⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    obtain ⟨rest,seen,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp pushed
    exact congrArg (·+1) (ih seen)

private theorem power_confidence {n κ : ℕ} (hn : 2≤n) :
    ENNReal.ofReal ((n:ℝ)^(-((κ+1:ℕ):ℝ))) +
      ENNReal.ofReal (((1:ℝ)/2)^EncodedVertexAmplification.confidenceExponent n (κ+1))
      ≤ ENNReal.ofReal ((n:ℝ)^(-(κ:ℝ))) := by
  have two : (2:ℝ)≤n := by exact_mod_cast hn
  have positive : (0:ℝ)<n := by linarith
  have half := EncodedVertexAmplification.confidence_power n (κ+1)
  rw [max_eq_right (by omega : 1≤n)] at half
  refine (add_le_add le_rfl (ENNReal.ofReal_le_ofReal half)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Nat.cast_add,Nat.cast_one,neg_add,Real.rpow_add positive,Real.rpow_neg_one]
  have hinv : (n:ℝ)⁻¹ ≤ (1:ℝ)/2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) two
  nlinarith [mul_le_mul_of_nonneg_left hinv (show 0≤(n:ℝ)^(-(κ:ℝ)) by positivity)]

def readBudgetFor {n : ℕ} (D : Input n) (T : ℕ) : ℕ :=
  readBudget n (inputWidth D) D.confidence+T*FairBitWords.width (rounds D)

theorem complete {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (tape : Bits) {q : ℕ}
    (within : Within q (tree (calibratedParameters k M (κ+1) adj w)
      (EncodedVertexAmplification.confidenceExponent n (κ+1)))) (enough : q≤tape.length) :
    ∃ out used, run k M κ adj w tape=some out ∧ out.suffix=tape.drop used ∧ used≤q := by
  obtain ⟨cut,used,selected,reads⟩ := EncodedSolverBits.complete within (tree_binary ..) tape enough
  have actual := run_observe k M κ adj w tape
  dsimp only at actual
  rw [selected] at actual
  cases h : run k M κ adj w tape with
  | none => simp [h] at actual
  | some out =>
    have eq : out.observe=(cut,tape.drop used) := by simpa only [h,Option.map_some,Option.some.injEq] using actual
    exact ⟨out,used,rfl,congrArg Prod.snd eq,reads⟩

theorem calibrated_selected (ε : ℝ) (positive : 0<ε) :
    ∃ k M : ℕ, 0<k ∧ 0<M ∧
    ∀ (n : ℕ), 2≤n → ∀ (adj : BinaryFractionalWalkOracle.Adjacency n)
      (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
      let D := calibratedParameters k M (κ+1) adj w
      let T := EncodedVertexAmplification.confidenceExponent n (κ+1)
      let q := readBudgetFor D T
      let p := (EncodedSolverBits.fairTape q).map (fun tape => ((run k M κ adj w tape).map Result.cut).join)
      p none ≤ ENNReal.ofReal ((n:ℝ)^(-(κ:ℝ))) ∧
      (∀ X, some X ∈ p.support → Good adj w X) ∧
      (∀ e, probability p (fun o => ∃ X ∈ o, e ∈ X) ≤ 8*(originalWeight adj w e:ℝ)*
        min (8*(M:ℝ)*(n:ℝ)^ε*(originalTotal adj w:ℝ)^(1/2:ℝ)) (8*(M:ℝ)*(n:ℝ)^(ε+1/3))*probability p (fun o => o.isSome)) ∧
      (∀ tape : Bits, q≤tape.length → ∃ out used,
        run k M κ adj w tape=some out ∧ out.suffix=tape.drop used ∧ used≤q) := by
  obtain ⟨k,M,hk,hM,calibrated⟩ := calibrated_best_families ε positive
  refine ⟨k,M,hk,hM,?_⟩
  intro n large adj w κ
  dsimp only
  let D := calibratedParameters k M (κ+1) adj w
  let T := EncodedVertexAmplification.confidenceExponent n (κ+1)
  let b := readBudget n (inputWidth D) D.confidence
  have factor : 1≤D.factor := calibrated_factor_ge_one hM adj w
  have familyWithin := familyTree_within (by omega : 0<n) D factor (input_fits D)
  obtain ⟨failed,scan⟩ := calibrated n large adj w (κ+1)
  have familyLaw := family_law familyWithin (familyTree_binary D)
  change (EncodedSolverBits.fairTape b).map
    (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join)=ideal (familyTree D) at familyLaw
  have supported (s : History (Edge n)) (hs : some s ∈ (ideal (familyTree D)).support) :
      s.cuts.length=rounds D ∧ (∀ X∈s.cuts, Good adj w X) ∧
        ∀ e, (CheckedMWHistory.occurrences s e:ℝ)/(s.cuts.length:ℝ) ≤ 8*(originalWeight adj w e:ℝ)*
          min (8*(M:ℝ)*(n:ℝ)^ε*(originalTotal adj w:ℝ)^(1/2:ℝ)) (8*(M:ℝ)*(n:ℝ)^(ε+1/3)) := by
    rw [← familyLaw] at hs
    obtain ⟨tape,ht,pick⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
    obtain ⟨res,used,ran,_,good⟩ := scan tape (tape_length ht).ge
    change EncodedSolverBits.run (familyTree D) tape=some (res,(tape.drop used,used)) at ran
    rw [ran] at pick
    exact good s pick
  have lengths (s) (hs) := (supported s hs).1
  have full := tree_within (by omega : 0<n) D factor (input_fits D) T lengths
  have fair := fair_law k M κ (readBudgetFor D T) adj w full
  rw [fair]
  refine ⟨?_,law_valid D T (fun s hs => (supported s hs).2.1),?_,fun tape ht => complete k M κ adj w tape full ht⟩
  · have original : (ideal (familyTree D)) none ≤ ENNReal.ofReal ((n:ℝ)^(-((κ+1:ℕ):ℝ))) :=
      (congrArg (fun p : PMF (Option (History (Edge n))) => p none) familyLaw) ▸ failed
    exact ((law_failure D T lengths).trans (add_le_add original le_rfl)).trans (power_confidence large)
  · intro e
    exact law_marginal D T e _ (by positivity) lengths (fun s hs => (supported s hs).2.2 e)


private theorem family_length {n k M j : ℕ} (hn : 0<n) (hM : 0<M)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (tape : Bits) {r : PhysicalBinaryEdgeFamily.Result n} {s : BinaryEdgeFamilyState.State n}
    (ran : BinaryEdgeFamilyCalibration.run k M j adj w tape=some r) (history : r.history=some s) :
    s.cuts.length=rounds (calibratedParameters k M j adj w) := by
  let D := calibratedParameters k M j adj w
  have compare := BinaryEdgeFamilyCalibration.run_observe k M j adj w tape
  rw [ran,Option.map_some] at compare
  change some r.observe=(EncodedSolverBits.run (familyTree D) tape).map _ at compare
  cases hr : EncodedSolverBits.run (familyTree D) tape with
  | none => simp [hr] at compare
  | some result =>
    rcases result with ⟨hist,rest,reads⟩
    rw [hr,Option.map_some] at compare
    have pair := Option.some.inj compare
    have hcut : some s.observe=hist := by
      have h := congrArg Prod.fst pair
      simpa only [PhysicalBinaryEdgeFamily.Result.observe,history,Option.map_some] using h
    have supported : some s.observe ∈ (ideal (familyTree D)).support :=
      hcut ▸ EncodedSolverBits.run_support (familyTree_binary D) hr
    have factor : 1≤D.factor := calibrated_factor_ge_one hM adj w
    exact (familyTree_spec hn D factor (D.factor : ℝ) (by positivity) (fun _ => le_rfl) s.observe supported).1

private theorem setup_paid (n κ : ℕ) :
    (samplingControl n κ).2.2 ≤ 2*BinaryRawRational.budget (n+κ+1)+24*(n+κ+2)^2+20 := by
  let C := n+κ+1
  let size := BinaryNaturalOperations.width n
  let next := BinaryNaturalOperations.add κ 1
  have hn : n.size ≤ C := (BinaryNaturalOperations.size_le_self _).trans (by unfold C; omega)
  have hc : κ.size ≤ C := (BinaryNaturalOperations.size_le_self _).trans (by unfold C; omega)
  have h1 : (1:ℕ).size ≤ C := (BinaryNaturalOperations.size_le_self _).trans (by unfold C; omega)
  have hns : (max 1 size.1).size ≤ C := by
    apply (BinaryNaturalOperations.size_le_self _).trans
    apply max_le (by unfold C; omega)
    exact (BinaryNaturalOperations.width_value _).trans_le hn
  have hcs : next.1.size ≤ C := (BinaryNaturalOperations.size_le_self _).trans
    ((BinaryNaturalOperations.add_value ..).trans_le (by unfold C; omega))
  have a := BinaryNaturalOperations.width_paid hn
  have b := BinaryNaturalOperations.add_paid hc h1
  have c := BinaryNaturalOperations.mul_paid hns hcs
  change next.2+size.2+(BinaryNaturalOperations.mul (max 1 size.1) next.1).2+8 ≤
    2*BinaryRawRational.budget C+24*(C+1)^2+20
  change size.2 ≤ _ at a
  change next.2 ≤ _ at b
  omega

private theorem confidence_le (n κ : ℕ) :
    EncodedVertexAmplification.confidenceExponent n (κ+1) ≤ (n+1)*(κ+1) := by
  have word : FairBitWords.width (max 1 n) ≤ n+1 := by
    have positive : 0 < max 1 n := (Nat.zero_lt_succ 0).trans_le (le_max_left ..)
    rw [← BinaryBoundedSampler.size_eq_width positive]
    exact (BinaryNaturalOperations.size_le_self _).trans (max_le (by omega) (by omega))
  exact Nat.mul_le_mul_right _ word

private def maxRounds {R : Type*} [Semiring R] (n B m : R) : R :=
  let width := B+m+n+n*n*(B+1)+3
  2*n*(2*n+n*n*(width+1)+3)+1

private theorem rounds_bound {n B k M κ : ℕ} (hk : 0<k)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (fit : AdaptiveWidthEnvelope.StoredWeights w B) :
    rounds (calibratedParameters k M κ adj w) ≤ maxRounds n B M.size := by
  refine (rounds_le _ (AdaptiveWidthEnvelope.calibrated_fits hk M κ adj w fit)).trans ?_
  unfold roundBudget AdaptiveWidthEnvelope.width maxRounds
  dsimp only
  have h : max B (M.size+n+n*n*(B+1)+3) ≤ B+M.size+n+n*n*(B+1)+3 := by
    apply max_le <;> omega
  gcongr

def tapeBound (n B M κ : ℕ) : ℕ :=
  readBudget n (AdaptiveWidthEnvelope.width n B M) (AdaptiveWidthEnvelope.confidence n B M (κ+1))+
    (n+1)*(κ+1)*(maxRounds n B M.size+1)

theorem tree_polynomial_reads {n k B : ℕ} (hn : 0<n) (hk : 0<k) (M κ : ℕ) (hM : 0<M)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (fit : AdaptiveWidthEnvelope.StoredWeights w B) :
    Within (tapeBound n B M κ) (tree (calibratedParameters k M (κ+1) adj w)
      (EncodedVertexAmplification.confidenceExponent n (κ+1))) := by
  let D := calibratedParameters k M (κ+1) adj w
  let T := EncodedVertexAmplification.confidenceExponent n (κ+1)
  have within := AdaptiveWidthEnvelope.family_polynomial_reads hn hk M (κ+1) hM adj w fit
  apply within_bind_support within (next T)
  intro s hs
  cases s with
  | none => exact .pure _ _
  | some s =>
    have factor : 1≤D.factor := calibrated_factor_ge_one hM adj w
    have length := (familyTree_spec hn D factor (D.factor:ℝ) (by positivity) (fun _ => le_rfl) s hs).1
    have pos : 0<s.cuts.length := length.symm ▸ rounds_pos D
    have width : FairBitWords.width s.cuts.length ≤ maxRounds n B M.size+1 := by
      rw [← BinaryBoundedSampler.size_eq_width pos,length]
      exact (BinaryNaturalOperations.size_le_self _).trans ((rounds_bound hk adj w fit).trans (Nat.le_succ _))
    have sample := BinaryFamilySampler.choose_within s.cuts T
    exact within_mono sample (Nat.mul_le_mul (confidence_le n κ) width)

def selectBudget {R : Type*} [Semiring R] (n B κ m : R) : R :=
  let r := maxRounds n B m
  2*BinaryRawRational.budget (n+κ+1)+24*(n+κ+2)^2+20+
    BinaryFamilySampler.budget r ((n+1)*(κ+1))+16*(r+1)^2

private theorem selected_work {n k M κ B : ℕ} (hn : 0<n) (hk : 0<k) (hM : 0<M)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (fit : AdaptiveWidthEnvelope.StoredWeights w B) (tape : Bits)
    {r : PhysicalBinaryEdgeFamily.Result n} (ran : BinaryEdgeFamilyCalibration.run k M (κ+1) adj w tape=some r)
    {cut : Option (Cut n)} {paid : ℕ} {rest : EncodedSolverBits.Tape}
    (sampled : EncodedSolverBits.run
      (select (EncodedVertexAmplification.confidenceExponent n (κ+1)) (r.history.map BinaryEdgeFamilyState.State.cuts))
      r.suffix=some ((cut,paid),rest)) :
    (samplingControl n κ).2.2+paid ≤ selectBudget n B κ M.size := by
  let T := EncodedVertexAmplification.confidenceExponent n (κ+1)
  let H := maxRounds n B M.size
  have m := setup_paid n κ
  have p : paid ≤ BinaryFamilySampler.budget H ((n+1)*(κ+1))+16*(H+1)^2 := by
    cases hist : r.history with
    | none =>
      simp only [hist,Option.map_none,select] at sampled
      change some (((none : Option (Cut n)),0),(r.suffix,0))=some ((cut,paid),rest) at sampled
      have hp := congrArg Prod.fst (Option.some.inj sampled)
      have zero : paid=0 := (congrArg Prod.snd hp).symm
      simp [zero]
    | some s =>
      simp only [hist,Option.map_some,select] at sampled
      have hit := EncodedSolverBits.run_support (BinaryFamilySampler.choose_binary s.cuts T) sampled
      have paidBound := (BinaryFamilySampler.choose_supported _ _ hit).2
      apply paidBound.trans
      have size : s.cuts.length ≤ H := by
        rw [family_length hn hM adj w tape ran hist]
        exact rounds_bound (M:=M) (κ:=κ+1) hk adj w fit
      have cb := confidence_le n κ
      unfold BinaryFamilySampler.budget BinaryFamilySampler.listCharge
      gcongr
  unfold selectBudget
  dsimp only
  change paid ≤ BinaryFamilySampler.budget (maxRounds n B M.size) ((n+1)*(κ+1))+
    16*(maxRounds n B M.size+1)^2 at p
  omega

open Polynomial in
theorem run_polynomial {k : ℕ} (hk : 0<k) (M : ℕ) (hM : 0<M) :
    ∃ p : Polynomial ℕ, ∀ {n B : ℕ}, 0<n → ∀ (κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
      (w : RationalEdgeThresholds.Weights n), AdaptiveWidthEnvelope.StoredWeights w B →
      ∀ (tape : Bits) {r : Result n}, run k M κ adj w tape=some r →
        r.familyPaid+r.samplePaid ≤ p.eval (n+B+κ) := by
  obtain ⟨p,work⟩ := BinaryEdgeFamilyCalibration.run_polynomial hk M
  refine ⟨p.comp (X+1)+selectBudget X X X (C M.size),?_⟩
  intro n B hn κ adj w fit tape r ran
  let controls := samplingControl n κ
  change (BinaryEdgeFamilyCalibration.run k M controls.1 adj w tape).bind (fun family =>
    (EncodedSolverBits.run (select controls.2.1 (family.history.map BinaryEdgeFamilyState.State.cuts)) family.suffix).map
      fun ((cut,paid),(rest,_)) => ⟨cut,rest,family.total+controls.2.2,paid⟩)=some r at ran
  obtain ⟨family,found,tail⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨⟨⟨cut,paid⟩,rest,reads⟩,selected,rfl⟩ := Option.map_eq_some_iff.mp tail
  simp only [controls,(controls_eq n κ).1] at found
  simp only [controls,(controls_eq n κ).2] at selected
  have raw := work (κ+1) adj w fit tape found
  have extra := selected_work hn hk hM adj w fit tape found selected
  let x := n+B+κ
  have mono : selectBudget n B κ M.size ≤ selectBudget x x x M.size := by
    have hn' : n≤x := by unfold x; omega
    have hB : B≤x := by unfold x; omega
    have hκ : κ≤x := by unfold x; omega
    unfold selectBudget maxRounds BinaryFamilySampler.budget BinaryRawRational.budget
    dsimp only
    gcongr
  have eval : (selectBudget X X X (C M.size)).eval x=selectBudget x x x M.size := by
    simp only [selectBudget,maxRounds,BinaryFamilySampler.budget,BinaryRawRational.budget,
      eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X,eval_C]
  rw [eval_add,eval_comp,eval_add,eval_X,eval_one,eval]
  change family.total+controls.2.2+paid ≤ p.eval (x+1)+selectBudget x x x M.size
  change family.total ≤ p.eval (x+1) at raw
  rw [Nat.add_assoc]
  exact Nat.add_le_add raw (extra.trans mono)

end DirectedFlowCutGap.BinaryWeakDecomposition
