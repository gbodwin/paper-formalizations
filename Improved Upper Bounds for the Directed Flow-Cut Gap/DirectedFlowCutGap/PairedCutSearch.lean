import DirectedFlowCutGap.EncodedSolverBits
import DirectedFlowCutGap.BinaryCutPriceSelection

/-! Run two cut algorithms on the same sequential fair source and return the
cheaper of their actual cuts. The second call starts at the first unread bit. -/
namespace DirectedFlowCutGap.PairedCutSearch

open scoped NNReal
open BinaryArithmetic BinaryRational FiniteDrawTrees FiniteAmplification

structure Result (A : Type) where
  output : A
  suffix : Bits
  paid : ℕ

def Result.observe {A : Type} (r : Result A) : A × Bits := (r.output,r.suffix)

def select {A : Type} (score : A → Fraction × ℕ) (a b : A) : A × ℕ :=
  let first := score a
  let second := score b
  let preferred := BinaryRational.le first.1 second.1
  (if preferred.1 then a else b,first.2+second.2+preferred.2+8)

theorem select_mem {A : Type} (score : A → Fraction × ℕ) (a b : A) :
    (select score a b).1=a ∨ (select score a b).1=b := by
  unfold select
  dsimp only
  split <;> simp

theorem select_price {A : Type} (score : A → Fraction × ℕ) (price : A → ℝ)
    (exactPrice : ∀ a, ((decode (score a).1).realValue : ℝ)=price a) (a b : A) :
    price (select score a b).1=min (price a) (price b) := by
  unfold select
  dsimp only
  have comparison : (BinaryRational.le (score a).1 (score b).1).1=true ↔ price a ≤ price b := by
    rw [BinaryRational.le_decode, RawNonnegativeRational.Code.le_eq_true,← exactPrice a,← exactPrice b]
    change _ ↔ (((decode (score a).1).value : ℝ≥0) : ℝ) ≤ (((decode (score b).1).value : ℝ≥0) : ℝ)
    norm_cast
  by_cases first : price a ≤ price b
  · rw [ite_eq_left (comparison.mpr first),min_eq_left first]
  · rw [ite_eq_right (fun h => first (comparison.mp h)),min_eq_right (le_of_not_ge first)]

theorem select_paid {A : Type} (score : A → Fraction × ℕ) {W C : ℕ}
    (fits : ∀ a, StoredBounded (score a).1 W ∧ (score a).2 ≤ C) (a b : A) :
    (select score a b).2 ≤ 2*C+2048*(W+1)^2+8 := by
  have ha := fits a
  have hb := fits b
  have cmp := BinaryRational.le_charge ha.1 hb.1
  change (score a).2+(score b).2+(BinaryRational.le (score a).1 (score b).1).2+8 ≤ _
  omega

def run {A : Type} (score : A → Fraction × ℕ) (mass size : Bits → Option (Result A))
    (tape : Bits) : Option (Result A) :=
  (mass tape).bind fun a => (size a.suffix).map fun b =>
    let chosen := select score a.output b.output
    ⟨chosen.1,b.suffix,a.paid+b.paid+chosen.2+8⟩

def tree {A : Type} (score : A → Fraction × ℕ) (mass size : FiniteDrawTrees.Tree A) : FiniteDrawTrees.Tree A :=
  FiniteDrawTrees.bind mass fun a => map (fun b => (select score a b).1) size

def observeTape {A : Type} (t : FiniteDrawTrees.Tree A) (bits : Bits) : Option (A × Bits) :=
  (EncodedSolverBits.run t bits).map (fun (a,(tail,_)) => (a,tail))

theorem run_observe {A : Type} (score : A → Fraction × ℕ) (mass size : Bits → Option (Result A))
    (first second : FiniteDrawTrees.Tree A)
    (hM : ∀ bits, (mass bits).map Result.observe=observeTape first bits)
    (hS : ∀ bits, (size bits).map Result.observe=observeTape second bits)
    (tape : Bits) : (run score mass size tape).map Result.observe=observeTape (tree score first second) tape := by
  unfold observeTape tree
  rw [show FiniteDrawTrees.bind first (fun a => map (fun b => (select score a b).1) second) =
    (first >>= fun a => map (fun b => (select score a b).1) second) from rfl,
    EncodedSolverBits.run_bind_observe]
  change (run score mass size tape).map Result.observe = (observeTape first tape).bind _
  rw [← hM]
  cases ra : mass tape with
  | none => simp [run,ra]
  | some a =>
    simp only [run,ra,Option.bind_some,Option.map_some,Result.observe]
    have same := congrArg (Option.map (fun (b,rest) => ((select score a.output b).1,rest))) (hS a.suffix)
    simp only [observeTape,EncodedSolverBits.run_map,Option.map_map,Function.comp_def] at same ⊢
    exact same

theorem complete {A : Type} (one : Bits → Option (Result A)) (t : FiniteDrawTrees.Tree A)
    (observes : ∀ bits, (one bits).map Result.observe=observeTape t bits)
    {k : ℕ} (within : Within k t) (binary : LazyFairBitTrees.Binary t)
    {valid : A → Prop} (legal : ∀ a ∈ (ideal t).support, valid a)
    (bits : Bits) (length : k ≤ bits.length) :
    ∃ r used, one bits=some r ∧ r.suffix=bits.drop used ∧ used≤k ∧ valid r.output := by
  obtain ⟨a,k',ran,hk⟩ := EncodedSolverBits.complete within binary bits length
  have same := observes bits
  simp only [observeTape,ran,Option.map_some] at same
  obtain ⟨r,hr,eq⟩ := Option.map_eq_some_iff.mp same
  have tail : r.suffix=bits.drop k' := congrArg Prod.snd eq
  have out : r.output=a := congrArg Prod.fst eq
  exact ⟨r,k',hr,tail,hk,out ▸ legal a (EncodedSolverBits.run_support binary ran)⟩

theorem fairTape {A : Type} (one : Bits → Option (Result A)) (t : FiniteDrawTrees.Tree A)
    (observes : ∀ bits, (one bits).map Result.observe=observeTape t bits)
    {k : ℕ} (within : Within k t) (binary : LazyFairBitTrees.Binary t) :
    (EncodedSolverBits.fairTape k).map (fun bits => (one bits).map Result.output)=(ideal t).map some := by
  rw [← EncodedSolverBits.run_fairTape within binary]
  apply congrArg ((EncodedSolverBits.fairTape k).map)
  funext bits
  simpa only [observeTape,Option.map_map,Function.comp_def,Result.observe] using
    congrArg (Option.map Prod.fst) (observes bits)

theorem run_paid {A : Type} (score : A → Fraction × ℕ) (mass size : Bits → Option (Result A))
    {P Q W C : ℕ} (paidMass : ∀ bits r, mass bits=some r → r.paid ≤ P)
    (paidSize : ∀ bits r, size bits=some r → r.paid ≤ Q)
    (fits : ∀ a, StoredBounded (score a).1 W ∧ (score a).2 ≤ C)
    (bits : Bits) {r : Result A} (ran : run score mass size bits=some r) :
    r.paid ≤ P+Q+2*C+2048*(W+1)^2+16 := by
  cases first : mass bits with
  | none => simp [run,first] at ran
  | some a =>
    cases second : size a.suffix with
    | none => simp [run,first,second] at ran
    | some b =>
      have h := paidMass bits a first
      have h' := paidSize a.suffix b second
      have choose := select_paid score fits a.output b.output
      have out : run score mass size bits =
          some ⟨(select score a.output b.output).1,b.suffix,a.paid+b.paid+(select score a.output b.output).2+8⟩ := by
        simp [run,first,second]
      have eq := Option.some.inj (ran.symm.trans out)
      rw [eq]
      change a.paid+b.paid+(select score a.output b.output).2+8 ≤ _
      omega

theorem tree_within {A : Type} {k l : ℕ} {mass size : FiniteDrawTrees.Tree A}
    (hM : Within k mass) (hS : Within l size) (score : A → Fraction × ℕ) :
    Within (k+l) (tree score mass size) :=
  within_bind hM _ (fun _ => within_map hS _)

theorem tree_binary {A : Type} {mass size : FiniteDrawTrees.Tree A}
    (hM : LazyFairBitTrees.Binary mass) (hS : LazyFairBitTrees.Binary size) (score : A → Fraction × ℕ) :
    LazyFairBitTrees.Binary (tree score mass size) :=
  LazyFairBitTrees.binary_bind hM _ (fun _ => LazyFairBitTrees.binary_map hS _)

private noncomputable def pairs {A : Type} (mass size : FiniteDrawTrees.Tree A) : PMF (A × A) :=
  (ideal mass).bind (fun a => (ideal size).map fun b => (a,b))

private theorem first_marginal {A : Type} (mass size : FiniteDrawTrees.Tree A) :
    (pairs mass size).map Prod.fst=ideal mass := by
  simp only [pairs,PMF.map_bind,PMF.map_comp]
  change (ideal mass).bind (fun a => (ideal size).map (Function.const A a))=ideal mass
  simp only [PMF.map_const,PMF.bind_pure]

private theorem second_marginal {A : Type} (mass size : FiniteDrawTrees.Tree A) :
    (pairs mass size).map Prod.snd=ideal size := by
  simp only [pairs,PMF.map_bind,PMF.map_comp]
  change (ideal mass).bind (fun _ => (ideal size).map id)=ideal size
  simp only [PMF.map_id,PMF.bind_const]

private theorem ideal_select {A : Type} (mass size : FiniteDrawTrees.Tree A) (score : A → Fraction × ℕ) :
    ideal (tree score mass size)=(pairs mass size).map (fun (a,b) => (select score a b).1) := by
  simp only [tree,law_bind,law_map,pairs,PMF.map_bind,PMF.map_comp,Function.comp_def]

theorem support {A : Type} (mass size : FiniteDrawTrees.Tree A) (score : A → Fraction × ℕ)
    {a : A} (h : a ∈ (ideal (tree score mass size)).support) :
    a ∈ (ideal mass).support ∨ a ∈ (ideal size).support := by
  rw [ideal_select] at h
  obtain ⟨⟨left,right⟩,both,selected⟩ := PMF.mem_support_map_iff _ _ _ |>.mp h
  obtain ⟨l,hl,hr⟩ := PMF.mem_support_bind_iff _ _ _ |>.mp both
  obtain ⟨r,hr,paired⟩ := PMF.mem_support_map_iff _ _ _ |>.mp hr
  have eqL : l=left := congrArg Prod.fst paired
  have eqR : r=right := congrArg Prod.snd paired
  subst l
  subst r
  change (select score left right).1=a at selected
  rw [← selected]
  rcases select_mem score left right with eq | eq
  · exact Or.inl (eq.symm ▸ hl)
  · exact Or.inr (eq.symm ▸ hr)

private theorem event_mono {A : Type} (p : PMF A) {P Q : Set A} (h : P ⊆ Q) :
    (p.toOuterMeasure P).toReal ≤ (p.toOuterMeasure Q).toReal := by
  apply ENNReal.toReal_mono _ (p.toOuterMeasure.mono h)
  change p.toOuterMeasure Q ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact p.tsum_coe_indicator_ne_top Q

theorem probability_gt_zero_eq_zero {A : Type} (p : PMF A) (price : A → ℝ)
    (zero : ∀ a ∈ p.support, price a=0) :
    probability p (fun a => 0 < price a)=0 := by
  unfold probability
  rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_,ENNReal.toReal_zero]
  rw [Set.disjoint_left]
  intro a has positive
  exact (lt_irrefl (0 : ℝ)) (zero a has ▸ positive)

theorem scaled_min {C x y q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) :
    min (2*(C*x*q)) (2*(C*y*q))=2*C*min x y*q := by
  by_cases i : x ≤ y
  · rw [min_eq_left i,min_eq_left (by gcongr : 2*(C*x*q) ≤ 2*(C*y*q))]
    ring
  · have i' := le_of_not_ge i
    rw [min_eq_right i',min_eq_right (by gcongr : 2*(C*y*q) ≤ 2*(C*x*q))]
    ring

theorem failure_min {A : Type} (mass size : FiniteDrawTrees.Tree A) (score : A → Fraction × ℕ) (price : A → ℝ)
    (exactPrice : ∀ a, ((decode (score a).1).realValue : ℝ)=price a)
    {a b δ : ℝ} (hm : probability (ideal mass) (fun x => a < price x) ≤ δ)
    (hs : probability (ideal size) (fun x => b < price x) ≤ δ) :
    probability (ideal (tree score mass size)) (fun x => min a b < price x) ≤ δ := by
  unfold probability at *
  rw [ideal_select,PMF.toOuterMeasure_map_apply]
  by_cases regime : a ≤ b
  · rw [min_eq_left regime]
    rw [← first_marginal mass size,PMF.toOuterMeasure_map_apply] at hm
    exact (event_mono _ (fun ⟨l,r⟩ h =>
      (show a < min (price l) (price r) from (select_price score price exactPrice l r) ▸ h).trans_le
        (min_le_left _ _))).trans hm
  · rw [min_eq_right (le_of_not_ge regime)]
    rw [← second_marginal mass size,PMF.toOuterMeasure_map_apply] at hs
    exact (event_mono _ (fun ⟨l,r⟩ h =>
      (show b < min (price l) (price r) from (select_price score price exactPrice l r) ▸ h).trans_le
        (min_le_right _ _))).trans hs

end DirectedFlowCutGap.PairedCutSearch
