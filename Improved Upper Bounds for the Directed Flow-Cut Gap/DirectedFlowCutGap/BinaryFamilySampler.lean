import DirectedFlowCutGap.BinaryDrawTreeExecution
import DirectedFlowCutGap.EncodedSolverBits
import DirectedFlowCutGap.BinaryNaturalView

/-! Select an index from a finite family, retaining bounded rejection as
failure. Each successful index has exactly the same probability. -/
namespace DirectedFlowCutGap.BinaryFamilySampler

open scoped ENNReal
open BinaryArithmetic FiniteDrawTrees FiniteAmplification BitSamplerCoupling

private def fairBit : FiniteDrawTrees.Tree Bool :=
  .draw 2 (by decide) (fun i => .pure (i.val == 1))

private def optionalIndex {n : ℕ} (r : DefaultOutput n) : Option (Fin n) :=
  if r.failed then none else some r.value

private theorem map_twice {A B C : Type} (f : A → B) (g : B → C) (t : FiniteDrawTrees.Tree A) :
    map g (map f t)=map (g ∘ f) t := by
  induction t with
  | pure a => rfl
  | draw n positive next ih =>
    change FiniteDrawTrees.Tree.draw n positive (fun i => map g (map f (next i))) =
      .draw n positive (fun i => map (g ∘ f) (next i))
    exact congrArg (FiniteDrawTrees.Tree.draw n positive) (funext ih)

def index {n : ℕ} (positive : 0<n) (T : ℕ) : FiniteDrawTrees.Tree (Option (Fin n) × ℕ) :=
  let bound := BinaryNaturalView.encode n
  let fuel := BinaryNaturalView.encode T
  let pos : 0<value bound.1 := by rw [BinaryNaturalView.encode_value]; exact positive
  map (fun r =>
    let v := (BinaryBoundedSampler.observe r)
    (if v.failed then none else some (Fin.cast (BinaryNaturalView.encode_value n) v.value),
      bound.2+fuel.2+r.steps+8)) (BinaryBoundedSampler.draw fairBit bound.1 pos fuel.1)

private theorem index_cast {a b : ℕ} (eq : a=b) (h : 0<a) (T : ℕ) :
    map (fun r => (optionalIndex r).map (Fin.cast eq)) (LazyFairBitTrees.rejection a h T) =
      map optionalIndex (LazyFairBitTrees.rejection b (eq ▸ h) T) := by
  subst b
  simp only [Fin.cast_refl,Option.map_id_fun,id_eq]

theorem index_value {n : ℕ} (positive : 0<n) (T : ℕ) :
    map Prod.fst (index positive T)=map optionalIndex (LazyFairBitTrees.rejection n positive T) := by
  let bound := (BinaryNaturalView.encode n).1
  let fuel := (BinaryNaturalView.encode T).1
  let pos : 0<value bound := (BinaryNaturalView.encode_value n).symm ▸ positive
  let project (r : DefaultOutput (value bound)) := (optionalIndex r).map (Fin.cast (BinaryNaturalView.encode_value n))
  have observed : map BinaryBoundedSampler.observe (BinaryBoundedSampler.draw fairBit bound pos fuel)=
      LazyFairBitTrees.rejection (value bound) pos (value fuel) := BinaryDrawTreeExecution.draw_observe bound fuel pos
  have composed := congrArg (map project) observed
  rw [show value fuel=T from BinaryNaturalView.encode_value T] at composed
  have finish := index_cast (BinaryNaturalView.encode_value n) pos T
  rw [← finish]
  simp only [index,map_twice,Function.comp_def]
  simp only [map_twice,Function.comp_def] at composed
  rw [← composed]
  apply congrArg (fun f => map f (BinaryBoundedSampler.draw fairBit bound pos fuel))
  funext a
  unfold project optionalIndex
  split <;> rfl

private theorem within_before_map {A B : Type} {t : FiniteDrawTrees.Tree A} {f : A → B} {k : ℕ}
    (h : Within k (map f t)) : Within k t := by
  induction t generalizing k with
  | pure a => exact .pure k a
  | draw n positive next ih =>
    change Within k (.draw n positive (fun i => map f (next i))) at h
    cases h with
    | draw kids => exact .draw (fun i => ih i (kids i))

private theorem binary_before_map {A B : Type} {t : FiniteDrawTrees.Tree A} {f : A → B}
    (h : LazyFairBitTrees.Binary (map f t)) : LazyFairBitTrees.Binary t := by
  induction t with
  | pure a => exact .pure a
  | draw n positive next ih =>
    change LazyFairBitTrees.Binary (.draw n positive (fun i => map f (next i))) at h
    cases h with
    | draw kids => exact .draw (fun i => ih i (kids i))

theorem index_within {n : ℕ} (positive : 0<n) (T : ℕ) :
    Within (T*FairBitWords.width n) (index positive T) := by
  apply within_before_map (f := Prod.fst)
  rw [index_value]
  exact within_map (LazyFairBitTrees.rejection_within n positive T) _

theorem index_binary {n : ℕ} (positive : 0<n) (T : ℕ) : LazyFairBitTrees.Binary (index positive T) := by
  apply binary_before_map (f := Prod.fst)
  rw [index_value]
  exact LazyFairBitTrees.binary_map (LazyFairBitTrees.rejection_binary n positive T) _

theorem index_law {n : ℕ} (positive : 0<n) (T : ℕ) :
    (ideal (index positive T)).map Prod.fst=BoundedBitRejection.law n T := by
  let : NeZero n := ⟨positive.ne'⟩
  rw [← law_map,index_value,law_map]
  change (ideal (LazyFairBitTrees.rejection n positive T)).map optionalIndex=_
  rw [LazyFairBitTrees.rejection_law n positive T,PMF.map_comp]
  rw [← BoundedBitRejection.run_law n T]
  congr 1
  funext tape
  unfold optionalIndex fallbackRun
  cases h : (BoundedBitRejection.run n T tape).value <;> simp [h]

def budget {R : Type*} [Semiring R] (n T : R) : R :=
  16*(n+1)^2+16*(T+1)^2+2048*(T+1)*(2*T+n+2)^2+8

theorem index_paid {n : ℕ} (positive : 0<n) (T : ℕ) {r : Option (Fin n) × ℕ}
    (h : r ∈ (ideal (index positive T)).support) : r.2 ≤ budget n T := by
  simp only [index,law_map] at h
  obtain ⟨output,observed,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have raw := BinaryDrawTreeExecution.draw_cost _ _ _ observed
  have a := (BinaryNaturalView.encode_paid n).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.size_le.mpr Nat.lt_two_pow_self) 1) 2))
  have b := (BinaryNaturalView.encode_paid T).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.size_le.mpr Nat.lt_two_pow_self) 1) 2))
  have bound (k : ℕ) : (BinaryNaturalView.encode k).1.length≤k := by
    rw [BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have pay : output.steps ≤ 2048*(T+1)*(2*T+n+2)^2 := by
    apply raw.trans
    rw [BinarySamplerCost.instructionBound,BinaryNaturalView.encode_value]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have h := bound n
    have h' := bound T
    omega
  unfold budget
  dsimp only
  omega


def listCharge (n : ℕ) : ℕ := 16*(n+1)^2

def choose {A : Type} (xs : List A) (T : ℕ) : FiniteDrawTrees.Tree (Option A × ℕ) :=
  let a := xs.toArray
  if positive : 0<a.size then
    map (fun (i,paid) => (i.bind (fun j => a[j.val]?),paid+listCharge a.size)) (index positive T)
  else .pure (none,listCharge a.size)

theorem choose_within {A : Type} (xs : List A) (T : ℕ) :
    Within (T*FairBitWords.width xs.length) (choose xs T) := by
  unfold choose
  dsimp only
  split
  · exact within_map (index_within ‹0 < xs.toArray.size› T) _
  · exact .pure _ _

theorem choose_binary {A : Type} (xs : List A) (T : ℕ) : LazyFairBitTrees.Binary (choose xs T) := by
  unfold choose
  dsimp only
  split
  · exact LazyFairBitTrees.binary_map (index_binary ‹0 < xs.toArray.size› T) _
  · exact .pure _

private theorem getIndex_eq {A : Type} (xs : List A) (i : Option (Fin xs.length)) :
    i.bind (fun j => xs.toArray[j.val]?) = i.map xs.get := by
  cases i with
  | none => rfl
  | some j =>
    simp only [Option.bind_some,Option.map_some,List.getElem?_toArray,List.getElem?_eq_getElem j.isLt]
    rfl

theorem choose_law {A : Type} (xs : List A) (positive : 0<xs.length) (T : ℕ) :
    (ideal (choose xs T)).map Prod.fst =
      (BoundedBitRejection.law xs.length T).map (fun i => i.map xs.get) := by
  have a : 0 < xs.toArray.size := positive
  have law := congrArg (fun p => PMF.map (fun i => i.map xs.get) p) (index_law a T)
  rw [choose,dite_eq_left a]
  simp only [law_map,PMF.map_comp,Function.comp_def] at law ⊢
  have point : (fun r : Option (Fin xs.toArray.size) × ℕ => r.1.bind (fun j => xs.toArray[j.val]?)) =
      (fun r => r.1.map xs.get) := funext (fun r => getIndex_eq xs r.1)
  rw [point]
  exact law

theorem choose_used {A : Type} (xs : List A) (T : ℕ) (tape : List Bool)
    (enough : T*FairBitWords.width xs.length ≤ tape.length) :
    ∃ result paid used, EncodedSolverBits.run (choose xs T) tape =
      some ((result,paid),(tape.drop used,used)) ∧ used≤T*FairBitWords.width xs.length :=
  let ⟨(result,paid),used,e,h⟩ :=
    EncodedSolverBits.complete (choose_within xs T) (choose_binary xs T) tape enough
  ⟨result,paid,used,e,h⟩

theorem choose_supported {A : Type} (xs : List A) (T : ℕ) {r : Option A × ℕ}
    (h : r ∈ (ideal (choose xs T)).support) :
    (∀ item ∈ r.1, item ∈ xs) ∧ r.2 ≤ budget xs.length T + listCharge xs.length := by
  unfold choose at h
  dsimp only at h
  split at h
  · let visit (v : Option (Fin xs.toArray.size) × ℕ) :=
      (v.1.bind (fun j => xs.toArray[j.val]?),v.2+listCharge xs.toArray.size)
    change r ∈ (ideal (map visit (index ‹0 < xs.toArray.size› T))).support at h
    have moved : r ∈ ((ideal (index ‹0 < xs.toArray.size› T)).map visit).support :=
      law_map uniformDraw visit _ ▸ h
    obtain ⟨v,hit,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
    refine ⟨?_,Nat.add_le_add_right (index_paid ‹0 < xs.toArray.size› T hit) _⟩
    intro item found
    change item ∈ v.1.bind (fun j => xs.toArray[j.val]?) at found
    have indexed : item ∈ v.1.map xs.get := (getIndex_eq xs v.1) ▸ found
    cases j : v.1 with
    | none => simp [j] at indexed
    | some j' =>
      have eq : xs.get j' = item := by simpa only [j,Option.map_some,Option.mem_some_iff] using indexed
      exact eq ▸ List.get_mem xs j'
  · have eq : r = (none,listCharge xs.length) := by simpa [ideal,law] using h
    subst r
    simp

private theorem count_get {A : Type} (xs : List A) (P : A → Prop) [DecidablePred P] :
    (∑ i : Fin xs.length, if P (xs.get i) then 1 else 0) = xs.countP (fun x => decide (P x)) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons,List.countP_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero,List.get_cons_succ',ih,decide_eq_true_eq,Nat.add_comm]
    split <;> simp_all

theorem choose_marginal {A : Type} [Fintype A] (xs : List A) (positive : 0<xs.length) (T : ℕ)
    (P : A → Prop) [DecidablePred P] :
    probability ((ideal (choose xs T)).map Prod.fst) (fun o => ∃ a ∈ o, P a) =
      (1-(BoundedBitRejection.law xs.length T none).toReal) *
        ((xs.countP (fun a => decide (P a)) : ℝ) / (xs.length : ℝ)) := by
  classical
  rw [choose_law xs positive,probability,PMF.toOuterMeasure_map_apply]
  change probability (BoundedBitRejection.law xs.length T) (fun i => ∃ a ∈ i.map xs.get, P a)=_
  rw [probability_eq_sum,Fintype.sum_option]
  simp only [Option.map_none,Option.not_mem_none,false_and,exists_false,ite_false,zero_add,
    Option.map_some,Option.mem_some_iff,BoundedBitRejection.law_some_toReal]
  have event (i : Fin xs.length) : (∃ a, xs.get i = a ∧ P a) ↔ P (xs.get i) := by
    constructor
    · rintro ⟨_,rfl,h⟩
      exact h
    · intro h
      exact ⟨_,rfl,h⟩
  simp_rw [event]
  let ratio := (1-(BoundedBitRejection.law xs.length T none).toReal)/(xs.length : ℝ)
  have each (i : Fin xs.length) :
      (if P (xs.get i) then ratio else 0) = ((if P (xs.get i) then 1 else 0 : ℕ) : ℝ)*ratio := by
    split <;> simp_all
  change (∑ i, if P (xs.get i) then ratio else 0)=_
  simp_rw [each]
  rw [← Finset.sum_mul,← Nat.cast_sum,count_get xs P]
  dsimp only [ratio]
  ring

theorem choose_failure {A : Type} (xs : List A) (positive : 0<xs.length) (T : ℕ) :
    ((ideal (choose xs T)).map Prod.fst) none = BoundedBitRejection.law xs.length T none := by
  rw [choose_law xs positive,PMF.map_apply,tsum_fintype,Fintype.sum_option]
  simp

end DirectedFlowCutGap.BinaryFamilySampler
