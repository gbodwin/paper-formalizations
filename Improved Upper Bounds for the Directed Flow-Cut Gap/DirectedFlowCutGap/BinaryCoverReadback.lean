import DirectedFlowCutGap.PhysicalCoverAccess
import DirectedFlowCutGap.BinaryRawRational
import DirectedFlowCutGap.CachedScalarRead

/-! Charge validation and conversion at the point where a reached physical
record is read. The same lookup and list readers are used by both views. -/
namespace DirectedFlowCutGap.BinaryCoverReadback

open BinaryArithmetic ImmutableReferenceSimulation PhysicalCoverAccess
open PhysicalCoverReader (Plan)
open FractionalCoverRawCore (RawRow)
open RawNonnegativeRational (Code)

private theorem readList_length {A : Type} (get : Bits → Read (Cell Bits)) (item : Bits → Read A)
    {fuel : ℕ} {ptr : Bits} {xs : List A} (read : (readListWith get item fuel ptr).1=some xs) : xs.length < fuel := by
  induction fuel generalizing ptr xs with
  | zero => simp [readListWith] at read
  | succ k ih =>
    simp only [readListWith,Read.bind_value] at read
    obtain ⟨cell,_,cellRead⟩ := Option.bind_eq_some_iff.mp read
    cases cell with
    | flag b => simp at cellRead
    | nil =>
      simp only [Read.pure_value,Option.some.injEq] at cellRead
      simp [← cellRead]
    | pair head tail =>
      simp only [Read.bind_value] at cellRead
      obtain ⟨x,_,read⟩ := Option.bind_eq_some_iff.mp cellRead
      obtain ⟨ys,got,h⟩ := Option.bind_eq_some_iff.mp read
      simp only [Read.pure_value,Option.some.injEq] at h
      rw [← h,List.length_cons]
      exact Nat.succ_lt_succ (ih got)

private theorem readList_map {A B : Type} (get : Bits → Read (Cell Bits)) (first : Bits → Read A)
    (second : Bits → Read B) (f : A → B) (eq : ∀ p, (second p).1=(first p).1.map f)
    (fuel : ℕ) (ptr : Bits) :
    (readListWith get second fuel ptr).1=(readListWith get first fuel ptr).1.map (List.map f) := by
  induction fuel generalizing ptr with
  | zero => rfl
  | succ k ih =>
    simp only [readListWith,Read.bind_value]
    cases found : (get ptr).1 with
    | none => rfl
    | some cell =>
      cases cell with
      | flag _ => rfl
      | nil => rfl
      | pair head tail =>
        simp only [Option.bind_some,Read.bind_value,eq,ih]
        cases (first head).1 <;> cases (readListWith get first k tail).1 <;> rfl

private def rawFraction (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) : Read Code := do
  let .pair a b ← get root | Read.failure
  let num ← readWordWith get H a
  let den ← readWordWith get H b
  let checked := BinaryRational.fromBits num den
  let q ← (checked.1,checked.2)
  let out := BinaryRawRational.decode q
  (some out.1,out.2+8)

private theorem rawFraction_value (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) :
    (rawFraction get H root).1=(readFractionWith get H root).1.map BinaryRational.decode := by
  simp only [rawFraction,readFractionWith,Read.bind_value]
  cases found : (get root).1 with
  | none => rfl
  | some cell =>
    cases cell with
    | flag _ => rfl
    | nil => rfl
    | pair a b =>
      simp only [Option.bind_some,Read.bind_value]
      cases hnum : (readWordWith get H a).1 with
      | none => rfl
      | some num =>
        simp only [Option.bind_some]
        cases (readWordWith get H b).1 with
        | none => rfl
        | some den =>
          simp only [Option.bind_some,BinaryRawRational.decode_value]
          cases (BinaryRational.fromBits num den).1 <;> rfl

private def rawBest (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) : Read (RawRow n) := do
  let .pair _ next ← get root | Read.failure
  let .pair best _ ← get next | Read.failure
  let xs ← readListWith get (rawFraction get H) H best
  let length := xs.length
  let cost := 16*(length+1)^2+12*(n+length+1)
  if h : length=n then (some ⟨xs.toArray,by simpa using h⟩,cost) else (none,cost)

private theorem decodeList {n : ℕ} (xs : List BinaryRational.Fraction) (h : xs.length=n) :
    BinaryFractionalRows.decodeRow ⟨xs.toArray,by simpa using h⟩ =
      ⟨(xs.map BinaryRational.decode).toArray,by simpa using h⟩ := by
  apply Vector.ext
  intro i hi
  simp [BinaryFractionalRows.decodeRow,BinaryFractionalRows.get]

private theorem rawBest_value (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) :
    (rawBest n get H root).1=(readBestWith n get H root).1 := by
  simp only [rawBest,readBestWith,Read.bind_value]
  cases found : (get root).1 with
  | none => rfl
  | some cell =>
    cases cell with
    | flag _ => rfl
    | nil => rfl
    | pair a b =>
      simp only [Option.bind_some,Read.bind_value]
      cases header : (get b).1 with
      | none => rfl
      | some c =>
        cases c with
        | flag _ => rfl
        | nil => rfl
        | pair first tail =>
          simp only [Option.bind_some,Read.bind_value,readList_map get _ _ _
            (rawFraction_value get H)]
          cases (readListWith get (readFractionWith get H) H first).1 with
          | none => rfl
          | some xs =>
            simp only [Option.map_some,Option.bind_some]
            by_cases h : xs.length=n
            · simp only [List.length_map,dite_eq_left h,Read.pure_value,decodeList xs h]
            · simp only [List.length_map,dite_eq_right h,Read.failure_value]

private def obstruction (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) : Read (Plan n) := do
  let .pair first last ← get root | Read.failure
  let source ← readWordWith get H first
  let target ← readWordWith get H last
  let a := BinaryNaturalView.decode source
  let b := BinaryNaturalView.decode target
  let cost := a.2+b.2+12*(n+H+1)
  if h : a.1<n ∧ b.1<n then (some (.infeasible (⟨a.1,h.1⟩,⟨b.1,h.2⟩)),cost)
  else (none,cost)

private theorem obstruction_value (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) :
    (obstruction n get H root).1=(readObstructionWith n get H root).1 := by
  simp only [obstruction,readObstructionWith,Read.bind_value,BinaryNaturalView.decode_value]
  cases found : (get root).1 with
  | none => rfl
  | some cell =>
    cases cell with
    | flag _ => rfl
    | nil => rfl
    | pair a b =>
      simp only [Option.bind_some,Read.bind_value]
      cases (readWordWith get H a).1 with
      | none => rfl
      | some s =>
        simp only [Option.bind_some]
        cases (readWordWith get H b).1 with
        | none => rfl
        | some t =>
          simp only [Option.bind_some]
          split <;> rfl

private def mask (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) : Read (Plan n) := do
  let word ← readWordWith get H root
  let length := word.length
  let cost := 16*(length+1)^2+12*(n+length+1)
  if h : length=n then (some (.zero ⟨word.toArray,by simpa using h⟩),cost) else (none,cost)

private theorem mask_value (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) :
    (mask n get H root).1=(readMaskWith n get H root).1 := by
  simp only [mask,readMaskWith,Read.bind_value]
  cases (readWordWith get H root).1 with
  | none => rfl
  | some w =>
    simp only [Option.bind_some]
    split <;> rfl

private def planWith (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) : Read (Plan n) := do
  match ← get root with
  | .nil => pure .invalid
  | .flag _ => Read.failure
  | .pair tag payload =>
    match ← get tag with
    | .flag false => obstruction n get H payload
    | .flag true => mask n get H payload
    | .nil => do
      let rows ← readListWith get (rawBest n get H) H payload
      pure (.covers rows)
    | .pair _ _ => Read.failure

private theorem planWith_value (n : ℕ) (get : Bits → Read (Cell Bits)) (H : ℕ) (root : Bits) :
    (planWith n get H root).1=(readPlanWith n get H root).1 := by
  simp only [planWith,readPlanWith,Read.bind_value]
  cases found : (get root).1 with
  | none => rfl
  | some cell =>
    cases cell with
    | flag _ => rfl
    | nil => rfl
    | pair tag payload =>
      simp only [Option.bind_some,Read.bind_value]
      cases (get tag).1 with
      | none => rfl
      | some c =>
        cases c with
        | pair _ _ => rfl
        | flag b => cases b <;> simp only [Option.bind_some,obstruction_value,mask_value]
        | nil =>
          have h := readList_map get (readBestWith n get H) (rawBest n get H) id
            (fun p => by simp only [rawBest_value,Option.map_id_fun,id_eq]) H payload
          simp only [List.map_id_fun,Option.map_id_fun,id_eq] at h
          simp only [Option.bind_some,Read.bind_value,h]

def readPlan (n : ℕ) (heap : Heap) : Bits → Read (Plan n) := planWith n (access heap) heap.length

def readPlanCached (n : ℕ) (s : CachedReferenceHeap.Store) : Bits → Read (Plan n) :=
  planWith n (fun address => (CachedScalarRead.read s address).1) s.cells.size

theorem readPlan_value (n : ℕ) (heap : Heap) (root : Bits) :
    (readPlan n heap root).1=(PhysicalCoverAccess.readPlan n heap root).1 :=
  planWith_value n (access heap) heap.length root

theorem readPlanCached_eq (n : ℕ) (s : CachedReferenceHeap.Store) (root : Bits) :
    readPlanCached n s root=readPlan n s.cells.toList root := by
  have h : (fun address => (CachedScalarRead.read s address).1) = access s.cells.toList :=
    funext fun address => (CachedScalarRead.value_eq s address).trans (CachedReferenceHeap.read_eq s address)
  simp only [readPlanCached,readPlan,h,Array.length_toList]

private theorem word_length (get : Bits → Read (Cell Bits)) {H : ℕ} {root word : Bits}
    (read : (readWordWith get H root).1=some word) : word.length < H :=
  readList_length get _ read

private structure AccessBound (get : Bits → Read (Cell Bits)) (width fee : ℕ) : Prop where
  charge : ∀ {root}, root.length ≤ width → (get root).2 ≤ fee
  fields : ∀ {root a b}, (get root).1 = some (.pair a b) → a.length ≤ width ∧ b.length ≤ width

private theorem list_charge {A : Type} {get : Bits → Read (Cell Bits)} {item : Bits → Read A}
    {width fee itemFee : ℕ} (model : AccessBound get width fee)
    (bounded : ∀ address, address.length ≤ width → (item address).2 ≤ itemFee)
    (fuel : ℕ) (root : Bits) (fits : root.length ≤ width) :
    (readListWith get item fuel root).2 ≤ fuel*(fee+itemFee) := by
  induction fuel generalizing root with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
      rw [readListWith,Nat.succ_mul]
      refine (Read.bind_bound (model.charge fits) (later:=itemFee+fuel*(fee+itemFee)) ?_).trans (by omega)
      intro cell found
      cases cell with
      | nil => exact Nat.zero_le _
      | flag _ => exact Nat.zero_le _
      | pair first rest =>
          obtain ⟨a,b⟩ := model.fields found
          apply Read.bind_bound (bounded first a)
          intro _ _
          exact (Read.bind_bound (ih rest b) (later:=0) (fun _ _ => Nat.zero_le _)).trans (by omega)

private theorem word_charge {get : Bits → Read (Cell Bits)} {width fee limit : ℕ}
    (model : AccessBound get width fee) {root : Bits} (fits : root.length ≤ width) :
    (readWordWith get limit root).2 ≤ limit*(fee+fee) := by
  unfold readWordWith
  apply list_charge model _ limit root fits
  intro address inside
  let flag : Cell Bits → Read Bool := fun
    | .flag bit => pure bit
    | _ => Read.failure
  change ((get address) >>= flag).2 ≤ fee
  have paid := Read.bind_bound (k:=flag) (model.charge inside) (later:=0)
    (fun cell _ => by cases cell <;> exact Nat.zero_le _)
  simpa only [Nat.add_zero] using paid

private def fractionExtra {R : Type*} [Semiring R] (H : R) : R := 64*(H+1)^2

private def arrayExtra {R : Type*} [Semiring R] (H B : R) : R := 16*(H+1)^2+12*(B+H+1)

private def endpointExtra {R : Type*} [Semiring R] (H B : R) : R := 32*(H+1)^2+12*(B+H+1)

private def cellBudget {R : Type*} [Semiring R] (H B : R) : R := 64*(H+1)*(B+1)

private def wordBudget {R : Type*} [Semiring R] (H fee : R) : R := H*(fee+fee)

private def fractionBudget {R : Type*} [Semiring R] (H fee : R) : R :=
  fee+wordBudget H fee+wordBudget H fee+fractionExtra H

private def bestBudget {R : Type*} [Semiring R] (H B fee : R) : R :=
  2*fee+H*(fee+fractionBudget H fee)+arrayExtra H B

def budgetAt {R : Type*} [Semiring R] (H B fee : R) : R :=
  2*fee+fractionBudget H fee+arrayExtra H B+endpointExtra H B+H*(fee+bestBudget H B fee)

def budget {R : Type*} [Semiring R] (H B : R) : R := budgetAt H B (cellBudget H B)

theorem budget_mono {H H' B B' : ℕ} (h : H ≤ H') (b : B ≤ B') :
    budget H B ≤ budget H' B' := by
  unfold budget budgetAt bestBudget fractionBudget wordBudget cellBudget arrayExtra endpointExtra fractionExtra
  gcongr

open Polynomial in
theorem budget_eval (H B : Polynomial ℕ) (x : ℕ) :
    (budget H B).eval x = budget (H.eval x) (B.eval x) := by
  simp only [budget,budgetAt,bestBudget,fractionBudget,wordBudget,cellBudget,arrayExtra,endpointExtra,
    fractionExtra,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat]

private theorem rawFraction_charge {get : Bits → Read (Cell Bits)} {root : Bits} {H B fee : ℕ}
    (model : AccessBound get B fee) (hr : root.length ≤ B) :
    (rawFraction get H root).2 ≤ fractionBudget H fee := by
  let W := wordBudget H fee
  let more := fractionExtra H
  unfold rawFraction fractionBudget
  refine (Read.bind_bound (model.charge hr) (later := W+W+more) ?_).trans (by
    change fee+(W+W+more) ≤ fee+W+W+more
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair a b =>
    have ptr : a.length≤B ∧ b.length≤B := model.fields found
    have ha : (readWordWith get H a).2 ≤ W := word_charge model ptr.1
    have hb : (readWordWith get H b).2 ≤ W := word_charge model ptr.2
    apply (Read.bind_bound ha (later := W+more) ?_).trans (by omega)
    intro num hnum
    apply Read.bind_bound hb
    intro den hden
    have numLength := word_length get hnum
    have denLength := word_length get hden
    have validate := (BinaryRational.fromBits_charge num den).trans
      (Nat.mul_le_mul_left 12 (show den.length+1 ≤ H+1 by omega))
    have extra : 12*(H+1)+(40*(H+1)^2+8) ≤ more := by
      unfold more fractionExtra
      nlinarith only
    refine (Read.bind_bound validate (later := 40*(H+1)^2+8) ?_).trans extra
    intro q returned
    obtain ⟨n,d⟩ := BinaryRational.fromBits_fields num den returned
    apply Nat.add_le_add_right
    exact BinaryRawRational.decode_paid (show BinaryRational.StoredBounded q H from
      ⟨n.symm ▸ numLength.le,d.symm ▸ denLength.le⟩)

private theorem rawBest_charge (n : ℕ) {get : Bits → Read (Cell Bits)} {root : Bits} {H B fee : ℕ} (hn : n ≤ B)
    (model : AccessBound get B fee) (hr : root.length ≤ B) :
    (rawBest n get H root).2 ≤ bestBudget H B fee := by
  let c := fee
  let table := H*(c+fractionBudget H fee)
  let extra := arrayExtra H B
  unfold rawBest bestBudget
  refine (Read.bind_bound (model.charge hr) (later := c+table+extra) ?_).trans (by
    change c+_ ≤ 2*c+table+extra
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair _ next =>
    have hnxt : next.length ≤ B := (show _ ∧ _ from model.fields found).2
    refine (Read.bind_bound (model.charge hnxt) (later := table+extra) ?_).trans (by
      change c+_ ≤ c+table+extra
      omega)
    intro cell found
    cases cell with
    | flag _ => exact Nat.zero_le _
    | nil => exact Nat.zero_le _
    | pair best _ =>
      have ptr : best.length ≤ B := (show _ ∧ _ from model.fields found).1
      have rows : (readListWith get (rawFraction get H) H best).2 ≤ table :=
        list_charge model (fun _ h => rawFraction_charge model h) H best ptr
      apply Read.bind_bound rows
      intro xs observed
      have len := (readList_length get _ observed).le
      dsimp only
      split <;> (change 16*(xs.length+1)^2+12*(n+xs.length+1) ≤ extra
                 unfold extra arrayExtra
                 gcongr)

private theorem obstruction_charge (n : ℕ) {get : Bits → Read (Cell Bits)} {root : Bits} {H B fee : ℕ} (hn : n ≤ B)
    (model : AccessBound get B fee) (hr : root.length ≤ B) :
    (obstruction n get H root).2 ≤
      fee+wordBudget H fee+wordBudget H fee+endpointExtra H B := by
  let W := wordBudget H fee
  let extra := endpointExtra H B
  unfold obstruction
  refine (Read.bind_bound (model.charge hr) (later := W+W+extra) ?_).trans (by
    change fee+_ ≤ fee+W+W+extra
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair a b =>
    have ptr : a.length≤B ∧ b.length≤B := model.fields found
    have ha : (readWordWith get H a).2 ≤ W := word_charge model ptr.1
    have hb : (readWordWith get H b).2 ≤ W := word_charge model ptr.2
    refine (Read.bind_bound ha (later := W+extra) ?_).trans (by omega)
    intro s hs
    apply Read.bind_bound hb
    intro t ht
    have src := (BinaryNaturalView.decode_paid s).trans
      (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right (word_length get hs).le 1) 2))
    have dst := (BinaryNaturalView.decode_paid t).trans
      (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right (word_length get ht).le 1) 2))
    dsimp only
    split <;> (change (BinaryNaturalView.decode s).2+(BinaryNaturalView.decode t).2+12*(n+H+1) ≤ extra
               unfold extra endpointExtra
               omega)

private theorem mask_charge (n : ℕ) {get : Bits → Read (Cell Bits)} {root : Bits} {H B fee : ℕ} (hn : n ≤ B)
    (model : AccessBound get B fee) (hr : root.length ≤ B) :
    (mask n get H root).2 ≤ wordBudget H fee+arrayExtra H B := by
  unfold mask
  have word : (readWordWith get H root).2 ≤ wordBudget H fee := word_charge model hr
  apply Read.bind_bound word
  intro bits observed
  have len := (word_length get observed).le
  dsimp only
  split <;> (dsimp only; unfold arrayExtra; gcongr)

private theorem plan_charge (n : ℕ) {get : Bits → Read (Cell Bits)} {root : Bits} {H B fee : ℕ} (hn : n ≤ B)
    (model : AccessBound get B fee) (hr : root.length ≤ B) :
    (planWith n get H root).2 ≤ budgetAt H B fee := by
  let c := fee
  let rows := H*(c+bestBudget H B fee)
  let extra := fractionBudget H fee+arrayExtra H B+endpointExtra H B+rows
  unfold planWith budgetAt
  refine (Read.bind_bound (model.charge hr) (later := c+extra) ?_).trans (by
    change c+(c+extra) ≤ 2*c+fractionBudget H fee+arrayExtra H B+endpointExtra H B+rows
    unfold extra
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair tag payload =>
    have ptr : tag.length≤B ∧ payload.length≤B := model.fields found
    apply Read.bind_bound (model.charge ptr.1)
    intro cell _
    cases cell with
    | pair _ _ => exact Nat.zero_le _
    | nil =>
      have items : (readListWith get (rawBest n get H) H payload).2 ≤ rows :=
        list_charge model (fun _ h => rawBest_charge n hn model h) H payload ptr.2
      refine (Read.bind_bound items (later:=0) (fun _ _ => Nat.zero_le _)).trans ?_
      unfold extra
      omega
    | flag b =>
      cases b with
      | false =>
        apply (obstruction_charge n hn model ptr.2).trans
        change c+wordBudget H fee+wordBudget H fee+endpointExtra H B ≤ extra
        unfold extra fractionBudget
        omega
      | true =>
        apply (mask_charge n hn model ptr.2).trans
        change wordBudget H fee+arrayExtra H B ≤ extra
        unfold extra fractionBudget
        omega

theorem readPlan_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ} (hn : n ≤ B)
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readPlan n heap root).2 ≤ budget heap.length B :=
  plan_charge n hn ⟨fun h => access_charge hh h, fun seen => lookup_bounded hh seen⟩ hr

private theorem list_same_result {A : Type} {first second : Bits → Read (Cell Bits)}
    {f g : Bits → Read A} (same : ∀ addr, (first addr).1=(second addr).1)
    (items : ∀ addr, (f addr).1=(g addr).1) (fuel : ℕ) (root : Bits) :
    (readListWith first f fuel root).1=(readListWith second g fuel root).1 := by
  induction fuel generalizing root with
  | zero => rfl
  | succ fuel ih =>
      simp only [readListWith,Read.bind_value,same]
      apply congrArg (fun k => (second root).1.bind k)
      funext cell
      cases cell with
      | nil => rfl
      | flag _ => rfl
      | pair _ _ => simp only [Read.bind_value,items,ih]

private theorem word_same_result {first second : Bits → Read (Cell Bits)}
    (same : ∀ addr, (first addr).1=(second addr).1) (H : ℕ) (root : Bits) :
    (readWordWith first H root).1=(readWordWith second H root).1 := by
  unfold readWordWith
  apply list_same_result same _ H root
  intro address
  let flag : Cell Bits → Read Bool := fun
    | .flag bit => pure bit
    | _ => Read.failure
  change ((first address) >>= flag).1 = ((second address) >>= flag).1
  simp only [Read.bind_value,same]

private theorem plan_same_result (n H : ℕ) (root : Bits) {first second : Bits → Read (Cell Bits)}
    (same : ∀ addr, (first addr).1=(second addr).1) :
    (planWith n first H root).1=(planWith n second H root).1 := by
  have words := word_same_result same H
  have fractions (addr : Bits) : (rawFraction first H addr).1=(rawFraction second H addr).1 := by
    simp only [rawFraction,Read.bind_value,same]
    apply congrArg (fun k => (second addr).1.bind k)
    funext cell
    cases cell with
    | nil => rfl
    | flag _ => rfl
    | pair _ _ => simp only [Read.bind_value,words]
  have rows (addr : Bits) : (rawBest n first H addr).1=(rawBest n second H addr).1 := by
    simp only [rawBest,Read.bind_value,same]
    apply congrArg (fun k => (second addr).1.bind k)
    funext cell
    cases cell with
    | nil => rfl
    | flag _ => rfl
    | pair _ tail =>
        simp only [Read.bind_value,same]
        apply congrArg (fun k => (second tail).1.bind k)
        funext child
        cases child with
        | nil => rfl
        | flag _ => rfl
        | pair _ _ => simp only [Read.bind_value,list_same_result same fractions]
  have ends (addr : Bits) : (obstruction n first H addr).1=(obstruction n second H addr).1 := by
    simp only [obstruction,Read.bind_value,same]
    apply congrArg (fun k => (second addr).1.bind k)
    funext cell
    cases cell with
    | nil => rfl
    | flag _ => rfl
    | pair _ _ => simp only [Read.bind_value,words]
  have flags (addr : Bits) : (mask n first H addr).1=(mask n second H addr).1 := by
    simp only [mask,Read.bind_value,words]
  simp only [planWith,Read.bind_value,same]
  apply congrArg (fun k => (second root).1.bind k)
  funext cell
  cases cell with
  | nil => rfl
  | flag _ => rfl
  | pair tag _ =>
      simp only [Read.bind_value,same]
      apply congrArg (fun k => (second tag).1.bind k)
      funext child
      cases child with
      | nil => simp only [Read.bind_value,list_same_result same rows]
      | flag b => cases b <;> first | apply ends | apply flags
      | pair _ _ => rfl

private def measuredAccess (s : CachedReferenceHeap.Store) (addr : Bits) : Read (Cell Bits) :=
  let read := CachedScalarRead.read s addr
  (read.1.1,read.1.2+read.2)

/-- The same terminal parser, charging the binary metadata work at each
cached access as well as the previously recorded work. -/
def readPlanWithBitCharge (n : ℕ) (s : CachedReferenceHeap.Store) (root : Bits) : Read (Plan n) :=
  planWith n (measuredAccess s) s.cells.size root

theorem readPlanWithBitCharge_value (n : ℕ) (s : CachedReferenceHeap.Store) (root : Bits) :
    (readPlanWithBitCharge n s root).1=(readPlanCached n s root).1 :=
  plan_same_result n s.cells.size root (fun _ => rfl)

def measuredBudget (H B : ℕ) : ℕ :=
  budgetAt H B (cellBudget H B+CachedScalarRead.budget (CachedHeapWidths.readerWidth H B))

theorem measuredBudget_mono {H H' B B' : ℕ} (size : H ≤ H') (length : B ≤ B') :
    measuredBudget H B ≤ measuredBudget H' B' := by
  have width : CachedHeapWidths.readerWidth H B ≤ CachedHeapWidths.readerWidth H' B' := by
    unfold CachedHeapWidths.readerWidth
    apply max_le_max length
    apply Nat.size_le_size
    have cells : H+1 ≤ H'+1 := Nat.add_le_add_right size 1
    have overall := max_le_max length (Nat.size_le_size cells)
    gcongr
  unfold measuredBudget budgetAt cellBudget CachedScalarRead.budget
    bestBudget fractionBudget wordBudget arrayExtra endpointExtra fractionExtra
  gcongr

private theorem measured_access_paid (s : CachedReferenceHeap.Store) {addr : Bits} {B : ℕ}
    (heap : Heap.Bounded B s.cells.toList) (width : addr.length ≤ B) :
    (CachedScalarRead.read s addr).2 ≤ CachedScalarRead.budget (CachedHeapWidths.readerWidth s.cells.size B) := by
  by_cases inside : value addr<s.cells.size
  · exact CachedScalarRead.paid le_rfl heap addr width inside
  · let W := CachedHeapWidths.readerWidth s.cells.size B
    have sizes := CachedHeapWidths.read_width le_rfl heap addr width
    have outside := fun ok => inside ((CachedBinaryIndex.values s.cells.size addr).2.2.2.mp ok)
    unfold CachedScalarRead.read
    rw [ite_eq_right outside]
    exact (CachedBinaryIndex.paid addr (width.trans (le_max_left _ _)) sizes.1).trans (by
      change 128*(W+2)^2≤CachedScalarRead.budget W
      unfold CachedScalarRead.budget
      omega)

theorem readPlanWithBitCharge_paid (n : ℕ) (s : CachedReferenceHeap.Store) (root : Bits) {B : ℕ}
    (hn : n≤B) (heap : Heap.Bounded B s.cells.toList) (width : root.length≤B) :
    (readPlanWithBitCharge n s root).2 ≤ measuredBudget s.cells.size B := by
  apply plan_charge n hn _ width
  constructor
  · intro addr fits
    have legacy := access_charge heap fits
    change (lookup addr s.cells.toList).2 ≤ cellBound s.cells.toList.length B at legacy
    rw [← CachedReferenceHeap.read_eq, ← CachedScalarRead.value_eq] at legacy
    exact Nat.add_le_add (by simpa only [cellBound,cellBudget,Array.length_toList] using legacy)
      (measured_access_paid s heap fits)
  · intro addr a b seen
    change (CachedScalarRead.read s addr).1.1 = some (.pair a b) at seen
    rw [CachedScalarRead.value_eq,CachedReferenceHeap.read_eq] at seen
    exact lookup_bounded heap seen

end DirectedFlowCutGap.BinaryCoverReadback
