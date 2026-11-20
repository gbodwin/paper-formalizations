import DirectedFlowCutGap.CachedBinaryAppend

/-! Execute the cached instruction's indexes and numerical fees through the
binary readers and appenders. Other instructions keep their established
reference implementation. -/
namespace DirectedFlowCutGap.CachedBinaryAttempt

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal EncodedSequenceAccess
open CachedReferenceExecution (FastState FastResult FastAttempt)
open CachedScalarRead (sumMeasured sum_value sum_paid)

private def allocate {C : ℕ} (s : FastState C) (dst : Reg) (cell : Cell Bits)
    (pc : Fin C) (events : List Event) : FastResult C × ℕ :=
  let next := increment true s.next
  let address := copyBits s.next
  let update := CachedBinaryAppend.append s.store cell
  let charge := sumMeasured [update.1.2,next.2,address.2,controlCost C]
  (⟨{s with store := update.1.1, next := next.1, registers := s.registers.set dst address.1, pc := pc},
    events,charge.1⟩,update.2+charge.2)

def attempt {C : ℕ} (p : Program C) (s : FastState C) : FastAttempt C × ℕ :=
  match p s.pc with
  | .make dst recipe pc =>
      let result := allocate s dst (recipe.cell s.registers) pc []
      (.completed result.1,result.2)
  | .request dst pc =>
      let bit := s.source.headD false
      let result := allocate {s with source := s.source.tail} dst (.flag bit) pc [.request bit]
      (.completed result.1,result.2)
  | .branch src nil flagFalse flagTrue pair =>
      let address := copyBits (s.registers.get src)
      let read := CachedScalarRead.read s.store address.1
      let charge := sumMeasured [address.2,read.1.2,controlCost C]
      match read.1.1 with
      | none => (.stopped s charge.1,read.2+charge.2)
      | some cell => (.completed ⟨{s with pc := tagBranch nil flagFalse flagTrue pair cell},[],charge.1⟩,
          read.2+charge.2)
  | .field dst src right pc =>
      let address := copyBits (s.registers.get src)
      let read := CachedScalarRead.read s.store address.1
      match read.1.1 with
      | some (.pair a b) =>
          let word := copyBits (if right then b else a)
          let charge := sumMeasured [address.2,read.1.2,word.2,controlCost C]
          (.completed ⟨{s with registers := s.registers.set dst word.1, pc := pc},[],charge.1⟩,read.2+charge.2)
      | _ =>
          let charge := sumMeasured [address.2,read.1.2,controlCost C]
          (.stopped s charge.1,read.2+charge.2)
  | .emit src pc =>
      let address := copyBits (s.registers.get src)
      let read := CachedScalarRead.read s.store address.1
      let charge := sumMeasured [address.2,read.1.2,controlCost C]
      match read.1.1 with
      | some (.flag value) => (.completed ⟨{s with pc := pc},[.emit value],charge.1⟩,read.2+charge.2)
      | _ => (.stopped s charge.1,read.2+charge.2)
  | _ => (CachedReferenceExecution.attempt p s,0)

private theorem allocation_value {C : ℕ} (s : FastState C) (dst : Reg) (cell : Cell Bits)
    (pc : Fin C) (events : List Event) :
    let after := increment true s.next
    let address := copyBits s.next
    let updated := CachedReferenceHeap.append s.store cell
    (allocate s dst cell pc events).1=
      ⟨{s with store := updated.1, next := after.1, registers := s.registers.set dst address.1, pc := pc},
        events,updated.2+after.2+address.2+controlCost C⟩ := by
  simp only [allocate,CachedBinaryAppend.value_eq,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]

theorem value_eq {C : ℕ} (p : Program C) (s : FastState C) :
    (attempt p s).1=CachedReferenceExecution.attempt p s := by
  cases label : p s.pc with
  | halt => simp only [attempt,label]
  | move dst src pc => simp only [attempt,label]
  | call pc ret dst => simp only [attempt,label]
  | ret src => simp only [attempt,label]
  | make dst recipe pc =>
      simp only [attempt,label,allocation_value,CachedReferenceExecution.attempt]
      cases s
      rfl
  | request dst pc =>
      simp only [attempt,label,allocation_value,CachedReferenceExecution.attempt]
      cases s
      rfl
  | branch src nil f t pair =>
      simp only [attempt,label,CachedReferenceExecution.attempt,CachedScalarRead.value_eq,sum_value,List.sum_cons,List.sum_nil,
        Nat.add_zero,Nat.add_assoc]
      cases (CachedReferenceHeap.read s.store (copyBits (s.registers.get src)).1).1 <;> rfl
  | field dst src right pc =>
      simp only [attempt,label,CachedReferenceExecution.attempt,CachedScalarRead.value_eq,sum_value,List.sum_cons,List.sum_nil,
        Nat.add_zero,Nat.add_assoc]
      cases (CachedReferenceHeap.read s.store (copyBits (s.registers.get src)).1).1 with
      | none => rfl
      | some loaded => cases loaded <;> rfl
  | emit src pc =>
      simp only [attempt,label,CachedReferenceExecution.attempt,CachedScalarRead.value_eq,sum_value,List.sum_cons,List.sum_nil,
        Nat.add_zero,Nat.add_assoc]
      cases (CachedReferenceHeap.read s.store (copyBits (s.registers.get src)).1).1 with
      | none => rfl
      | some loaded => cases loaded <;> rfl

attribute [local irreducible] CachedBinaryAppend.append CachedScalarRead.read CachedScalarRead.sumMeasured

def sumsBudget (width : ℕ) : ℕ := 4*(96*(width+2)^2+4)+1

private theorem sums_paid {parts : List ℕ} {width : ℕ} (short : parts.length≤4)
    (fit : (sumMeasured parts).1.size≤width) : (sumMeasured parts).2≤sumsBudget width := by
  rw [sum_value] at fit
  exact (sum_paid parts fit).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ short) 1)

private theorem read_metadata {H B : ℕ} (s : CachedReferenceHeap.Store) (address : Bits)
    (size : s.cells.size≤H) (fits : Heap.Bounded B s.cells.toList) (width : address.length≤B) :
    (CachedScalarRead.read s address).2≤CachedScalarRead.budget (CachedHeapWidths.readerWidth H B) := by
  by_cases inside : value address<s.cells.size
  · exact CachedScalarRead.paid size fits address width inside
  · let W := CachedHeapWidths.readerWidth H B
    have h := CachedHeapWidths.read_width size fits address width
    have wider : B≤W := le_max_left _ _
    have outside := fun ok => inside ((CachedBinaryIndex.values s.cells.size address).2.2.2.mp ok)
    unfold CachedScalarRead.read
    rw [ite_eq_right outside]
    exact (CachedBinaryIndex.paid address (width.trans wider) h.1).trans (by
      change 128*(W+2)^2≤CachedScalarRead.budget W
      unfold CachedScalarRead.budget
      omega)

private theorem allocation_paid {C H B W : ℕ} (s : FastState C) (dst : Reg) (cell : Cell Bits)
    (pc : Fin C) (events : List Event) (size : s.store.cells.size≤H)
    (heap : Heap.Bounded B s.store.cells.toList) (fits : cell.Bounded B)
    (charge : (allocate s dst cell pc events).1.cost.size≤W) :
    (allocate s dst cell pc events).2≤1200*(CachedHeapWidths.readerWidth (H+1) B+2)^2+sumsBudget W := by
  let added := CachedBinaryAppend.append s.store cell
  let terms := [added.1.2,(increment true s.next).2,(copyBits s.next).2,controlCost C]
  simp only [allocate] at charge ⊢
  have paid : (sumMeasured terms).1.size≤W := charge
  have work := sums_paid (parts:=terms) (by simp [terms]) paid
  exact Nat.add_le_add (CachedBinaryAppend.paid size heap fits) work

def budget (C H B : ℕ) : ℕ :=
  1200*(CachedHeapWidths.readerWidth (H+1) B+2)^2+
    CachedScalarRead.budget (CachedHeapWidths.readerWidth H B)+sumsBudget (stepBound C H B).size

set_option maxHeartbeats 900000 in
theorem paid {C H B : ℕ} (p : Program C) (s : FastState C) (fits : s.freeze.Bounded H B) :
    (attempt p s).2≤budget C H B := by
  have records := fits.1
  simp only [State.records,FastState.freeze,Array.length_toList] at records
  have size : s.store.cells.size≤H := by omega
  have heap : Heap.Bounded B s.store.cells.toList := fits.2.2.1
  have registers : s.registers.All (fun a => a.length≤B) := fits.2.2.2.1
  have read (src : Reg) : (CachedScalarRead.read s.store (copyBits (s.registers.get src)).1).2≤
      CachedScalarRead.budget (CachedHeapWidths.readerWidth H B) := by
    apply read_metadata _ _ size heap
    rw [(copyBits_spec _).1]
    exact Registers.get_all registers src
  have charge : (attempt p s).1.freeze.operations.size≤(stepBound C H B).size := by
    rw [value_eq,CachedReferenceExecution.attempt_eq]
    exact Nat.size_le_size (ImmutableReferenceTerminal.attempt_bound fits)
  have includeRead {q r : ℕ} (first : q≤CachedScalarRead.budget (CachedHeapWidths.readerWidth H B))
      (second : r≤sumsBudget (stepBound C H B).size) : q+r≤budget C H B := by
    unfold budget
    omega
  have includeAppend {q : ℕ} (bounded : q≤1200*(CachedHeapWidths.readerWidth (H+1) B+2)^2+
      sumsBudget (stepBound C H B).size) : q≤budget C H B := by
    unfold budget
    omega
  cases label : p s.pc with
  | make dst recipe pc =>
      simp only [attempt,label,FastAttempt.freeze,FastResult.freeze,success] at charge ⊢
      exact includeAppend (allocation_paid s dst (recipe.cell s.registers) pc [] size heap
        (recipe.bounded registers) charge)
  | request dst pc =>
      simp only [attempt,label,FastAttempt.freeze,FastResult.freeze,success] at charge ⊢
      let bit := s.source.headD false
      exact includeAppend (allocation_paid {s with source := s.source.tail} dst (.flag bit) pc [.request bit]
        size heap trivial charge)
  | branch src nil f t pair =>
      simp only [attempt,label] at charge ⊢
      cases looked : (CachedScalarRead.read s.store (copyBits (s.registers.get src)).1).1.1 <;>
        simp only [looked,FastAttempt.freeze,FastResult.freeze,stopped,success] at charge ⊢
      all_goals exact includeRead (read src) (sums_paid (by simp) charge)
  | field dst src right pc =>
      simp only [attempt,label] at charge ⊢
      cases looked : (CachedScalarRead.read s.store (copyBits (s.registers.get src)).1).1.1 with
      | none =>
          simp only [looked,FastAttempt.freeze,stopped] at charge ⊢
          exact includeRead (read src) (sums_paid (by simp) charge)
      | some cell =>
          cases cell <;> simp only [looked,FastAttempt.freeze,FastResult.freeze,stopped,success] at charge ⊢
          all_goals exact includeRead (read src) (sums_paid (by simp) charge)
  | emit src pc =>
      simp only [attempt,label] at charge ⊢
      cases looked : (CachedScalarRead.read s.store (copyBits (s.registers.get src)).1).1.1 with
      | none =>
          simp only [looked,FastAttempt.freeze,stopped] at charge ⊢
          exact includeRead (read src) (sums_paid (by simp) charge)
      | some cell =>
          cases cell <;> simp only [looked,FastAttempt.freeze,FastResult.freeze,stopped,success] at charge ⊢
          all_goals exact includeRead (read src) (sums_paid (by simp) charge)
  | _ => simp only [attempt,label,Nat.zero_le]

end DirectedFlowCutGap.CachedBinaryAttempt
