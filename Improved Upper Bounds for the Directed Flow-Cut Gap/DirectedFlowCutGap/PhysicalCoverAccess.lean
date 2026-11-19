import DirectedFlowCutGap.PhysicalCoverReader
import DirectedFlowCutGap.CachedReferenceHeap

/-!
# Charging terminal heap accesses during fractional-cover readback

The reader follows binary pointers in the original physical heap. The
charge is the sum of the actual reference lookups. Decoding and building
the returned Lean values have separate costs.
-/

namespace DirectedFlowCutGap.PhysicalCoverAccess

open BinaryArithmetic ImmutableReferenceSimulation RetainedGridState
open FractionalCoverRawCore

abbrev Read (A : Type) := Option A × ℕ

namespace Read

def failure {A : Type} : Read A := (none, 0)

def bind {A B : Type} (r : Read A) (k : A → Read B) : Read B :=
  match r.1 with
  | none => (none, r.2)
  | some a =>
    let next := k a
    (next.1, r.2 + next.2)

instance : Monad Read where
  pure a := (some a, 0)
  bind := bind

@[simp] theorem pure_value {A : Type} (a : A) : (pure a : Read A).1 = some a := rfl
@[simp] theorem pure_charge {A : Type} (a : A) : (pure a : Read A).2 = 0 := rfl
@[simp] theorem failure_value {A : Type} : (failure : Read A).1 = none := rfl
@[simp] theorem failure_charge {A : Type} : (failure : Read A).2 = 0 := rfl

theorem bind_value {A B : Type} (r : Read A) (k : A → Read B) :
    (r >>= k).1 = r.1.bind (fun a => (k a).1) := by
  change (bind r k).1 = _
  unfold bind
  cases r.1 <;> rfl

theorem bind_bound {A B : Type} {r : Read A} {k : A → Read B} {first later : ℕ}
    (hr : r.2 ≤ first) (hk : ∀ a, r.1 = some a → (k a).2 ≤ later) :
    (r >>= k).2 ≤ first + later := by
  change (bind r k).2 ≤ _
  unfold bind
  cases h : r.1 with
  | none => exact hr.trans (Nat.le_add_right _ _)
  | some a => exact Nat.add_le_add hr (hk a h)

end Read

def cellBound (H B : ℕ) : ℕ := 64 * (H + 1) * (B + 1)

def access (heap : Heap) (root : Bits) : Read (Cell Bits) := lookup root heap

private theorem access_result (heap : Heap) (root : Bits) :
    (eraseHeap heap)[value root]? = Option.map eraseCell (access heap root).1 :=
  (lookup_refines root heap).symm

theorem access_charge {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (access heap root).2 ≤ cellBound heap.length B := lookup_bound hr hh

def readListWith {A : Type} (get : Bits → Read (Cell Bits)) (item : Bits → Read A) :
    ℕ → Bits → Read (List A)
  | 0, _ => Read.failure
  | fuel + 1, root => do
    match ← get root with
    | .nil => pure []
    | .flag _ => Read.failure
    | .pair head tail =>
      let x ← item head
      let xs ← readListWith get item fuel tail
      pure (x :: xs)

def readList {A : Type} (heap : Heap) (item : Bits → Read A) : ℕ → Bits → Read (List A) :=
  readListWith (access heap) item

private theorem readList_value {A : Type} (heap : Heap) (item : Bits → Read A)
    (spec : ℕ → Option A) (h : ∀ address, (item address).1 = spec (value address))
    (fuel : ℕ) (root : Bits) :
    (readList heap item fuel root).1 =
      PhysicalCoverReader.readList (eraseHeap heap) spec fuel (value root) := by
  induction fuel generalizing root with
  | zero => rfl
  | succ fuel ih =>
    simp only [readList] at ih
    have he := access_result heap root
    cases hv : (access heap root).1 with
    | none => simp [readList, readListWith, PhysicalCoverReader.readList, Read.bind_value, he, hv]
    | some c =>
      cases c <;> simp [readList, readListWith, PhysicalCoverReader.readList, Read.bind_value, he, hv,
        eraseCell, Cell.map, h, ih]

theorem readList_charge {A : Type} {heap : Heap} {item : Bits → Read A}
    {B charge : ℕ} (hh : heap.Bounded B)
    (hi : ∀ address, address.length ≤ B → (item address).2 ≤ charge)
    (fuel : ℕ) (root : Bits) (hr : root.length ≤ B) :
    (readList heap item fuel root).2 ≤ fuel * (cellBound heap.length B + charge) := by
  induction fuel generalizing root with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    unfold readList readListWith
    rw [Nat.succ_mul]
    apply (Read.bind_bound (access_charge hh hr)
      (later := charge + fuel * (cellBound heap.length B + charge)) ?_).trans
    · omega
    · intro c hc
      cases c with
      | nil => exact Nat.zero_le _
      | flag b => exact Nat.zero_le _
      | pair head tail =>
        have hp : head.length ≤ B ∧ tail.length ≤ B := lookup_bounded hh hc
        apply Read.bind_bound (hi head hp.1)
        intro a _
        apply (Read.bind_bound (ih tail hp.2) (later := 0) ?_).trans
        · omega
        · intro _
          exact fun _ => Nat.zero_le _

private def readFlagWith (get : Bits → Read (Cell Bits)) (root : Bits) : Read Bool := do
  let .flag b ← get root | Read.failure
  pure b

private def readFlag (heap : Heap) : Bits → Read Bool := readFlagWith (access heap)

def readWordWith (get : Bits → Read (Cell Bits)) (length : ℕ) (root : Bits) : Read Bits :=
  readListWith get (readFlagWith get) length root

def readWord (heap : Heap) : Bits → Read Bits :=
  readWordWith (access heap) heap.length

theorem readWord_value (heap : Heap) (root : Bits) :
    (readWord heap root).1 = PhysicalCoverReader.readWord (eraseHeap heap) (value root) := by
  unfold readWord readWordWith PhysicalCoverReader.readWord
  have hlen : (eraseHeap heap).length = heap.length := by simp [eraseHeap]
  rw [hlen]
  apply readList_value
  intro address
  have he := access_result heap address
  change (readFlag heap address).1 =
    (match (eraseHeap heap)[value address]? with
      | some (.flag b) => some b
      | _ => none)
  unfold readFlag readFlagWith
  rw [Read.bind_value, he]
  cases (access heap address).1 with
  | none => rfl
  | some c => cases c <;> rfl

private theorem readWordWith_value (heap : Heap) (root : Bits) :
    (readWordWith (access heap) heap.length root).1 =
      PhysicalCoverReader.readWord (eraseHeap heap) (value root) := readWord_value heap root

private theorem readFlag_charge {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readFlag heap root).2 ≤ cellBound heap.length B := by
  unfold readFlag readFlagWith
  have h := Read.bind_bound (access_charge hh hr) (later := 0) (k := fun c =>
    match c with
    | .flag b => pure b
    | _ => Read.failure) (by intro c _; cases c <;> exact Nat.zero_le _)
  simpa only [Nat.add_zero] using h

def wordBound (H B : ℕ) : ℕ := H * (cellBound H B + cellBound H B)

theorem readWord_charge {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readWord heap root).2 ≤ wordBound heap.length B :=
  readList_charge hh (fun _ ha => readFlag_charge hh ha) _ _ hr

def readFractionWith (get : Bits → Read (Cell Bits)) (length : ℕ) (root : Bits) : Read BinaryRational.Fraction := do
  let .pair a b ← get root | Read.failure
  let num ← readWordWith get length a
  let den ← readWordWith get length b
  ((BinaryRational.fromBits num den).1, 0)

def readFraction (heap : Heap) : Bits → Read BinaryRational.Fraction :=
  readFractionWith (access heap) heap.length

theorem readFraction_value (heap : Heap) (root : Bits) :
    (readFraction heap root).1 = PhysicalCoverReader.readFraction (eraseHeap heap) (value root) := by
  have he := access_result heap root
  cases hr : (access heap root).1 with
  | none => simp [readFraction, readFractionWith, PhysicalCoverReader.readFraction, Read.bind_value, he, hr]
  | some c => cases c <;> simp [readFraction, readFractionWith, PhysicalCoverReader.readFraction,
      Read.bind_value, he, hr, eraseCell, Cell.map, readWordWith_value]

def fractionBound (H B : ℕ) : ℕ := cellBound H B + wordBound H B + wordBound H B

theorem readFraction_charge {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readFraction heap root).2 ≤ fractionBound heap.length B := by
  unfold readFraction readFractionWith fractionBound
  apply (Read.bind_bound (access_charge hh hr) (later := wordBound heap.length B + wordBound heap.length B) ?_).trans
  · omega
  · intro c hc
    cases c with
    | nil => exact Nat.zero_le _
    | flag b => exact Nat.zero_le _
    | pair a b =>
      have hb : a.length ≤ B ∧ b.length ≤ B := lookup_bounded hh hc
      apply Read.bind_bound (readWord_charge hh hb.1)
      intro num _
      simpa only [Nat.add_zero, readWord] using
        (Read.bind_bound (readWord_charge hh hb.2) (k := fun den => ((BinaryRational.fromBits num den).1, 0))
          (later := 0) (by intro _ _; exact Nat.zero_le _))

def readBestWith (n : ℕ) (get : Bits → Read (Cell Bits)) (length : ℕ) (root : Bits) : Read (RawRow n) := do
  let .pair _ next ← get root | Read.failure
  let .pair best _ ← get next | Read.failure
  let xs ← readListWith get (readFractionWith get length) length best
  if h : xs.length = n then
    pure (BinaryFractionalRows.decodeRow ⟨xs.toArray, by simpa using h⟩)
  else Read.failure

private def readBest (n : ℕ) (heap : Heap) : Bits → Read (RawRow n) :=
  readBestWith n (access heap) heap.length

private theorem readBest_value (n : ℕ) (heap : Heap) (root : Bits) :
    (readBest n heap root).1 = PhysicalCoverReader.readBest n (eraseHeap heap) (value root) := by
  have hroot := access_result heap root
  cases hr : (access heap root).1 with
  | none => simp [readBest, readBestWith, PhysicalCoverReader.readBest, Read.bind_value, hroot, hr]
  | some r =>
    cases r with
    | nil => simp [readBest, readBestWith, PhysicalCoverReader.readBest, Read.bind_value, hroot, hr, eraseCell, Cell.map]
    | flag b => simp [readBest, readBestWith, PhysicalCoverReader.readBest, Read.bind_value, hroot, hr, eraseCell, Cell.map]
    | pair first next =>
      have hnext := access_result heap next
      have hlen : (eraseHeap heap).length = heap.length := by simp [eraseHeap]
      cases ht : (access heap next).1 with
      | none => simp [readBest, readBestWith, PhysicalCoverReader.readBest, Read.bind_value, hroot, hr, hnext, ht,
          eraseCell, Cell.map]
      | some c =>
        have hread (r : Bits) := readList_value heap (readFraction heap) _ (readFraction_value heap) heap.length r
        simp only [readList, readFraction] at hread
        cases c <;> simp [readBest, readBestWith, PhysicalCoverReader.readBest, Read.bind_value, hroot, hr, hnext, ht,
          eraseCell, Cell.map, hlen, hread]
        congr 1
        funext xs
        split <;> rfl

def bestBound (H B : ℕ) : ℕ :=
  2 * cellBound H B + H * (cellBound H B + fractionBound H B)

private theorem readBest_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readBest n heap root).2 ≤ bestBound heap.length B := by
  unfold readBest readBestWith bestBound
  apply (Read.bind_bound (access_charge hh hr)
    (later := cellBound heap.length B + heap.length * (cellBound heap.length B + fractionBound heap.length B)) ?_).trans
  · omega
  · intro c hc
    cases c with
    | nil => exact Nat.zero_le _
    | flag b => exact Nat.zero_le _
    | pair _ next =>
      have hb : next.length ≤ B := (show _ ∧ _ from lookup_bounded hh hc).2
      apply Read.bind_bound (access_charge hh hb)
      intro d hd
      cases d with
      | nil => exact Nat.zero_le _
      | flag b => exact Nat.zero_le _
      | pair best _ =>
        have hbest : best.length ≤ B := (show _ ∧ _ from lookup_bounded hh hd).1
        have hrow := readList_charge hh (item := readFraction heap)
          (fun _ hptr => readFraction_charge hh hptr) heap.length best hbest
        apply (Read.bind_bound hrow (later := 0) ?_).trans (by simp)
        intro xs _
        split <;> exact Nat.zero_le _

open PhysicalCoverReader (Plan)

def readObstructionWith (n : ℕ) (get : Bits → Read (Cell Bits)) (length : ℕ) (root : Bits) : Read (Plan n) := do
  let .pair first last ← get root | Read.failure
  let source ← readWordWith get length first
  let target ← readWordWith get length last
  if h : value source < n ∧ value target < n then
    pure (.infeasible (⟨value source, h.1⟩, ⟨value target, h.2⟩))
  else Read.failure

def readMaskWith (n : ℕ) (get : Bits → Read (Cell Bits)) (length : ℕ) (root : Bits) : Read (Plan n) := do
  let a ← readWordWith get length root
  if h : a.length = n then pure (.zero ⟨a.toArray, by simpa using h⟩) else Read.failure

def readPlanWith (n : ℕ) (get : Bits → Read (Cell Bits)) (length : ℕ) (root : Bits) : Read (Plan n) := do
  match ← get root with
  | .nil => pure .invalid
  | .flag _ => Read.failure
  | .pair tag payload =>
    match ← get tag with
    | .flag false => readObstructionWith n get length payload
    | .flag true => readMaskWith n get length payload
    | .nil => do
      let rows ← readListWith get (readBestWith n get length) length payload
      pure (.covers rows)
    | .pair _ _ => Read.failure

private def readObstruction (n : ℕ) (heap : Heap) : Bits → Read (Plan n) :=
  readObstructionWith n (access heap) heap.length

private def readMask (n : ℕ) (heap : Heap) : Bits → Read (Plan n) :=
  readMaskWith n (access heap) heap.length

def readPlan (n : ℕ) (heap : Heap) : Bits → Read (Plan n) :=
  readPlanWith n (access heap) heap.length

def readPlanCached (n : ℕ) (s : CachedReferenceHeap.Store) : Bits → Read (Plan n) :=
  readPlanWith n (CachedReferenceHeap.read s) s.cells.size

theorem readPlanCached_eq (n : ℕ) (s : CachedReferenceHeap.Store) (root : Bits) :
    readPlanCached n s root = readPlan n s.cells.toList root := by
  have h : CachedReferenceHeap.read s = access s.cells.toList :=
    funext (CachedReferenceHeap.read_eq s)
  simp only [readPlanCached, readPlan, h, Array.length_toList]

theorem readPlan_value (n : ℕ) (heap : Heap) (root : Bits) :
    (readPlan n heap root).1 = PhysicalCoverReader.readPlan n (eraseHeap heap) (value root) := by
  have hroot := access_result heap root
  cases hr : (access heap root).1 with
  | none => simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, Read.bind_value, hroot, hr]
  | some c =>
    cases c with
    | nil => simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, Read.bind_value, hroot, hr, eraseCell, Cell.map]
    | flag b => simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, Read.bind_value, hroot, hr, eraseCell, Cell.map]
    | pair tag payload =>
      have htag := access_result heap tag
      have hlen : (eraseHeap heap).length = heap.length := by simp [eraseHeap]
      cases ht : (access heap tag).1 with
      | none => simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, Read.bind_value,
          hroot, hr, htag, ht, eraseCell, Cell.map]
      | some d =>
        cases d with
        | pair p q => simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, Read.bind_value,
            hroot, hr, htag, ht, eraseCell, Cell.map]
        | nil =>
          have hread := readList_value heap (readBest n heap) _ (readBest_value n heap) heap.length payload
          simp only [readList, readBest] at hread
          simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, Read.bind_value, hroot, hr, htag, ht,
            eraseCell, Cell.map, hlen, hread]
          cases PhysicalCoverReader.readList (eraseHeap heap)
            (PhysicalCoverReader.readBest n (eraseHeap heap)) heap.length (value payload) <;> rfl
        | flag bit =>
          cases bit with
          | true =>
            simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, readMaskWith, Read.bind_value, hroot, hr, htag, ht,
              eraseCell, Cell.map, readWordWith_value]
            congr 1
            funext a
            split <;> rfl
          | false =>
            have hp := access_result heap payload
            cases hpr : (access heap payload).1 with
            | none => simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, readObstructionWith, Read.bind_value,
                hroot, hr, htag, ht, hp, hpr, eraseCell, Cell.map]
            | some r =>
              cases r <;>
                simp [readPlan, readPlanWith, PhysicalCoverReader.readPlan, readObstructionWith, Read.bind_value,
                  hroot, hr, htag, ht, hp, hpr, eraseCell, Cell.map, readWordWith_value]
              congr 1
              funext s
              congr 1
              funext t
              change (if h : value s < n ∧ value t < n then
                  (pure (Plan.infeasible (⟨value s, h.1⟩, ⟨value t, h.2⟩)) : Read (Plan n))
                else Read.failure).1 =
                (if h : value s < n ∧ value t < n then
                  some (⟨value s, h.1⟩, ⟨value t, h.2⟩) else none).bind (fun d => some (.infeasible d))
              split <;> rfl

private theorem readObstruction_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readObstruction n heap root).2 ≤ fractionBound heap.length B := by
  unfold readObstruction fractionBound
  refine (Read.bind_bound (access_charge hh hr) (later := wordBound heap.length B + wordBound heap.length B)
    ?_).trans (by omega)
  intro c hc
  cases c with
  | nil => exact Nat.zero_le _
  | flag b => exact Nat.zero_le _
  | pair a b =>
    have hb : a.length ≤ B ∧ b.length ≤ B := lookup_bounded hh hc
    apply Read.bind_bound (readWord_charge hh hb.1)
    intro s _
    refine (Read.bind_bound (readWord_charge hh hb.2) (later := 0) ?_).trans (by simp)
    intro t _
    split <;> exact Nat.zero_le _

private theorem readMask_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readMask n heap root).2 ≤ wordBound heap.length B := by
  unfold readMask readMaskWith
  refine (Read.bind_bound (readWord_charge hh hr) (later := 0) ?_).trans (by simp)
  intro a _
  split <;> exact Nat.zero_le _

def planBound (H B : ℕ) : ℕ :=
  2 * cellBound H B + fractionBound H B + H * (cellBound H B + bestBound H B)

theorem readPlan_charge (n : ℕ) {heap : Heap} {root : Bits} {B : ℕ}
    (hh : heap.Bounded B) (hr : root.length ≤ B) :
    (readPlan n heap root).2 ≤ planBound heap.length B := by
  unfold readPlan readPlanWith planBound
  let later := fractionBound heap.length B + heap.length * (cellBound heap.length B + bestBound heap.length B)
  refine (Read.bind_bound (access_charge hh hr) (later := cellBound heap.length B + later) ?_).trans ?_
  · intro c hc
    cases c with
    | nil => exact Nat.zero_le _
    | flag b => exact Nat.zero_le _
    | pair tag payload =>
      have hp : tag.length ≤ B ∧ payload.length ≤ B := lookup_bounded hh hc
      apply Read.bind_bound (access_charge hh hp.1)
      intro c _
      cases c with
      | nil =>
        have h := readList_charge hh (item := readBest n heap)
          (fun _ h => readBest_charge n hh h) heap.length payload hp.2
        refine (Read.bind_bound h (later := 0) (by intro xs _; exact Nat.zero_le _)).trans ?_
        unfold later
        omega
      | flag bit =>
        cases bit with
        | false => exact (readObstruction_charge n hh hp.2).trans (Nat.le_add_right _ _)
        | true =>
          apply (readMask_charge n hh hp.2).trans
          unfold later fractionBound
          omega
      | pair _ _ => exact Nat.zero_le _
  · unfold later
    omega

end DirectedFlowCutGap.PhysicalCoverAccess
