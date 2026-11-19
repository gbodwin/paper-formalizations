import DirectedFlowCutGap.PhysicalCoverAccess
import DirectedFlowCutGap.BinaryRawRational

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
  planWith n (CachedReferenceHeap.read s) s.cells.size

theorem readPlan_value (n : ℕ) (heap : Heap) (root : Bits) :
    (readPlan n heap root).1=(PhysicalCoverAccess.readPlan n heap root).1 :=
  planWith_value n (access heap) heap.length root

theorem readPlanCached_eq (n : ℕ) (s : CachedReferenceHeap.Store) (root : Bits) :
    readPlanCached n s root=readPlan n s.cells.toList root := by
  have h : CachedReferenceHeap.read s = access s.cells.toList := funext (CachedReferenceHeap.read_eq s)
  simp only [readPlanCached,readPlan,h,Array.length_toList]

private theorem word_length (get : Bits → Read (Cell Bits)) {H : ℕ} {root word : Bits}
    (read : (readWordWith get H root).1=some word) : word.length < H :=
  readList_length get _ read

private def fractionExtra {R : Type*} [Semiring R] (H : R) : R := 64*(H+1)^2

private def arrayExtra {R : Type*} [Semiring R] (H B : R) : R := 16*(H+1)^2+12*(B+H+1)

private def endpointExtra {R : Type*} [Semiring R] (H B : R) : R := 32*(H+1)^2+12*(B+H+1)

private def cellBudget {R : Type*} [Semiring R] (H B : R) : R := 64*(H+1)*(B+1)

private def wordBudget {R : Type*} [Semiring R] (H B : R) : R :=
  H*(cellBudget H B+cellBudget H B)

private def fractionBudget {R : Type*} [Semiring R] (H B : R) : R :=
  cellBudget H B+wordBudget H B+wordBudget H B+fractionExtra H

private def bestBudget {R : Type*} [Semiring R] (H B : R) : R :=
  2*cellBudget H B+H*(cellBudget H B+fractionBudget H B)+arrayExtra H B

def budget {R : Type*} [Semiring R] (H B : R) : R :=
  2*cellBudget H B+fractionBudget H B+arrayExtra H B+endpointExtra H B+
    H*(cellBudget H B+bestBudget H B)

theorem budget_mono {H H' B B' : ℕ} (h : H ≤ H') (b : B ≤ B') :
    budget H B ≤ budget H' B' := by
  unfold budget bestBudget fractionBudget wordBudget cellBudget arrayExtra endpointExtra fractionExtra
  gcongr

open Polynomial in
theorem budget_eval (H B : Polynomial ℕ) (x : ℕ) :
    (budget H B).eval x = budget (H.eval x) (B.eval x) := by
  simp only [budget,bestBudget,fractionBudget,wordBudget,cellBudget,arrayExtra,endpointExtra,
    fractionExtra,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat]

private theorem rawFraction_charge {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (rawFraction (access heap) heap.length root).2 ≤ fractionBudget heap.length B := by
  let H := heap.length
  let W := wordBudget H B
  let more := fractionExtra H
  unfold rawFraction fractionBudget
  refine (Read.bind_bound (access_charge hh hr) (later := W+W+more) ?_).trans (by
    change cellBudget H B+(W+W+more) ≤ cellBudget H B+W+W+more
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair a b =>
    have ptr : a.length≤B ∧ b.length≤B := lookup_bounded hh found
    have ha : (readWordWith (access heap) H a).2 ≤ W := readWord_charge hh ptr.1
    have hb : (readWordWith (access heap) H b).2 ≤ W := readWord_charge hh ptr.2
    apply (Read.bind_bound ha (later := W+more) ?_).trans (by omega)
    intro num hnum
    apply Read.bind_bound hb
    intro den hden
    have numLength := word_length (access heap) hnum
    have denLength := word_length (access heap) hden
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

private theorem rawBest_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ} (hn : n ≤ B)
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (rawBest n (access heap) heap.length root).2 ≤ bestBudget heap.length B := by
  let H := heap.length
  let c := cellBudget H B
  let table := H*(c+fractionBudget H B)
  let extra := arrayExtra H B
  unfold rawBest bestBudget
  refine (Read.bind_bound (access_charge hh hr) (later := c+table+extra) ?_).trans (by
    change c+_ ≤ 2*c+table+extra
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair _ next =>
    have hnxt : next.length ≤ B := (show _ ∧ _ from lookup_bounded hh found).2
    refine (Read.bind_bound (access_charge hh hnxt) (later := table+extra) ?_).trans (by
      change c+_ ≤ c+table+extra
      omega)
    intro cell found
    cases cell with
    | flag _ => exact Nat.zero_le _
    | nil => exact Nat.zero_le _
    | pair best _ =>
      have ptr : best.length ≤ B := (show _ ∧ _ from lookup_bounded hh found).1
      have rows : (readListWith (access heap) (rawFraction (access heap) H) H best).2 ≤ table :=
        readList_charge hh (fun _ h => rawFraction_charge hh h) H best ptr
      apply Read.bind_bound rows
      intro xs observed
      have len := (readList_length (access heap) _ observed).le
      dsimp only
      split <;> (change 16*(xs.length+1)^2+12*(n+xs.length+1) ≤ extra
                 unfold extra arrayExtra
                 gcongr)

private theorem obstruction_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ} (hn : n ≤ B)
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (obstruction n (access heap) heap.length root).2 ≤
      cellBudget heap.length B+wordBudget heap.length B+wordBudget heap.length B+endpointExtra heap.length B := by
  let H := heap.length
  let W := wordBudget H B
  let extra := endpointExtra H B
  unfold obstruction
  refine (Read.bind_bound (access_charge hh hr) (later := W+W+extra) ?_).trans (by
    change cellBudget H B+_ ≤ cellBudget H B+W+W+extra
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair a b =>
    have ptr : a.length≤B ∧ b.length≤B := lookup_bounded hh found
    have ha : (readWordWith (access heap) H a).2 ≤ W := readWord_charge hh ptr.1
    have hb : (readWordWith (access heap) H b).2 ≤ W := readWord_charge hh ptr.2
    refine (Read.bind_bound ha (later := W+extra) ?_).trans (by omega)
    intro s hs
    apply Read.bind_bound hb
    intro t ht
    have src := (BinaryNaturalView.decode_paid s).trans
      (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right (word_length (access heap) hs).le 1) 2))
    have dst := (BinaryNaturalView.decode_paid t).trans
      (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right (word_length (access heap) ht).le 1) 2))
    dsimp only
    split <;> (change (BinaryNaturalView.decode s).2+(BinaryNaturalView.decode t).2+12*(n+H+1) ≤ extra
               unfold extra endpointExtra
               omega)

private theorem mask_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ} (hn : n ≤ B)
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (mask n (access heap) heap.length root).2 ≤ wordBudget heap.length B+arrayExtra heap.length B := by
  unfold mask
  have word : (readWordWith (access heap) heap.length root).2 ≤ wordBudget heap.length B := readWord_charge hh hr
  apply Read.bind_bound word
  intro bits observed
  have len := (word_length (access heap) observed).le
  dsimp only
  split <;> (dsimp only; unfold arrayExtra; gcongr)

theorem readPlan_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ} (hn : n ≤ B)
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readPlan n heap root).2 ≤ budget heap.length B := by
  let H := heap.length
  let c := cellBudget H B
  let rows := H*(c+bestBudget H B)
  let extra := fractionBudget H B+arrayExtra H B+endpointExtra H B+rows
  unfold readPlan planWith budget
  refine (Read.bind_bound (access_charge hh hr) (later := c+extra) ?_).trans (by
    change c+(c+extra) ≤ 2*c+fractionBudget H B+arrayExtra H B+endpointExtra H B+rows
    unfold extra
    omega)
  intro cell found
  cases cell with
  | flag _ => exact Nat.zero_le _
  | nil => exact Nat.zero_le _
  | pair tag payload =>
    have ptr : tag.length≤B ∧ payload.length≤B := lookup_bounded hh found
    apply Read.bind_bound (access_charge hh ptr.1)
    intro cell _
    cases cell with
    | pair _ _ => exact Nat.zero_le _
    | nil =>
      have items : (readListWith (access heap) (rawBest n (access heap) H) H payload).2 ≤ rows :=
        readList_charge hh (fun _ h => rawBest_charge n hn hh h) H payload ptr.2
      refine (Read.bind_bound items (later:=0) (fun _ _ => Nat.zero_le _)).trans ?_
      unfold extra
      omega
    | flag b =>
      cases b with
      | false =>
        apply (obstruction_charge n hn hh ptr.2).trans
        change c+wordBudget H B+wordBudget H B+endpointExtra H B ≤ extra
        unfold extra fractionBudget
        omega
      | true =>
        apply (mask_charge n hn hh ptr.2).trans
        change wordBudget H B+arrayExtra H B ≤ extra
        unfold extra fractionBudget
        omega

end DirectedFlowCutGap.BinaryCoverReadback
