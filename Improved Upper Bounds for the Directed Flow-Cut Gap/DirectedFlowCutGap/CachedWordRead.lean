import DirectedFlowCutGap.CachedScalarRead
import DirectedFlowCutGap.PhysicalCoverAccess

/-! Follow the actual cached Boolean-list reader with the prior observation
and a separate count of the binary index and counter operations. -/
namespace DirectedFlowCutGap.CachedWordRead

open BinaryArithmetic ImmutableReferenceSimulation
open PhysicalCoverAccess (Read)
open CachedReferenceHeap (Store)

abbrev Counted (α : Type) := Read α × ℕ

private def pure {α : Type} (value : α) : Counted α := ((some value,0),0)
private def failure {α : Type} : Counted α := ((none,0),0)

private def andThen {α β : Type} (part : Counted α) (next : α → Counted β) : Counted β :=
  match part.1.1 with
  | none => ((none,part.1.2),part.2)
  | some value =>
      let result := next value
      ((result.1.1,part.1.2+result.1.2),part.2+result.2)

private theorem prior_andThen {α β : Type} (part : Counted α) (next : α → Counted β) :
    (andThen part next).1=Read.bind part.1 (fun value => (next value).1) := by
  unfold andThen Read.bind
  cases part.1.1 <;> rfl

private theorem seen_andThen {α β : Type} (part : Counted α) (next : α → Counted β) {found : β}
    (seen : (andThen part next).1.1=some found) :
    ∃ value, part.1.1=some value ∧ (next value).1.1=some found ∧
      (andThen part next).2=part.2+(next value).2 := by
  unfold andThen at seen ⊢
  cases outcome : part.1.1 with
  | none => simp only [outcome,reduceCtorEq] at seen
  | some a => exact ⟨a,rfl,by simpa only [outcome] using seen,rfl⟩

private def fetch (s : Store) (address : Bits) : Counted (Cell Bits) := CachedScalarRead.read s address

private theorem fetch_eq (s : Store) (address : Bits) :
    (fetch s address).1=CachedReferenceHeap.read s address := CachedScalarRead.value_eq s address

private def flag (s : Store) (address : Bits) : Counted Bool :=
  andThen (fetch s address) fun known => match known with
    | .flag value => pure value
    | _ => failure

private theorem flag_eq (s : Store) (address : Bits) :
    (flag s address).1=Read.bind (CachedReferenceHeap.read s address) (fun known => match known with
      | .flag value => (Pure.pure value : Read Bool)
      | _ => Read.failure) := by
  simp only [flag,prior_andThen,fetch_eq]
  apply congrArg (Read.bind (CachedReferenceHeap.read s address))
  funext cell
  cases cell <;> rfl

def word (s : Store) : ℕ → Bits → Counted Bits
  | 0,_ => failure
  | fuel+1,address => andThen (fetch s address) fun known => match known with
    | .nil => pure []
    | .flag _ => failure
    | .pair head tail => andThen (flag s head) fun bit =>
        andThen (word s fuel tail) fun rest => pure (bit::rest)

theorem word_eq (s : Store) (fuel : ℕ) (address : Bits) :
    (word s fuel address).1=PhysicalCoverAccess.readWordWith (CachedReferenceHeap.read s) fuel address := by
  induction fuel generalizing address with
  | zero => rfl
  | succ fuel ih =>
      simp only [PhysicalCoverAccess.readWordWith] at ih
      simp only [word,PhysicalCoverAccess.readWordWith,PhysicalCoverAccess.readListWith,prior_andThen,fetch_eq]
      apply congrArg (Read.bind (CachedReferenceHeap.read s address))
      funext result
      cases result with
      | nil => rfl
      | flag bit => rfl
      | pair head tail =>
          simp only [prior_andThen,flag_eq,ih]
          rfl

def loadBudget (H B : ℕ) : ℕ := CachedScalarRead.budget (CachedHeapWidths.readerWidth H B)

private theorem got_bound {s : Store} {H B : ℕ} (size : s.cells.size≤H)
    (fits : Heap.Bounded B s.cells.toList) {address : Bits} (wordSize : address.length≤B)
    {cell : Cell Bits} (done : (fetch s address).1.1=some cell) :
    cell.Bounded B ∧ (fetch s address).2≤loadBudget H B := by
  rw [fetch_eq] at done
  have inside := CachedHeapWidths.returned_address done
  have charged := CachedScalarRead.paid size fits address wordSize inside
  rw [CachedReferenceHeap.read_eq] at done
  exact ⟨lookup_bounded fits done,charged⟩

private theorem flag_paid {s : Store} {H B : ℕ} (size : s.cells.size≤H)
    (fits : Heap.Bounded B s.cells.toList) {address : Bits} (wordSize : address.length≤B)
    {bit : Bool} (done : (flag s address).1.1=some bit) :
    (flag s address).2≤loadBudget H B := by
  unfold flag at done ⊢
  obtain ⟨cell,loaded,followed,fee⟩ := seen_andThen _ _ done
  rw [fee]
  have h := (got_bound size fits wordSize loaded).2
  cases cell <;> simpa only [pure,failure,Nat.add_zero] using h

/-- For every successfully read word, all visited pointers are in bounds and
both per-link/cache reads are charged at their certified binary widths. -/
theorem word_paid {s : Store} {H B : ℕ} (size : s.cells.size≤H)
    (fits : Heap.Bounded B s.cells.toList) (fuel : ℕ) {address : Bits} (wordSize : address.length≤B)
    {bits : Bits} (done : (word s fuel address).1.1=some bits) :
    (word s fuel address).2≤fuel*(2*loadBudget H B) := by
  induction fuel generalizing address bits with
  | zero => cases done
  | succ fuel ih =>
      rw [word] at done ⊢
      obtain ⟨cell,loaded,followed,fee⟩ := seen_andThen _ _ done
      rw [fee,Nat.succ_mul]
      obtain ⟨bounded,first⟩ := got_bound size fits wordSize loaded
      cases cell with
      | nil =>
          change (fetch s address).2+0≤_
          omega
      | flag bit =>
          change (fetch s address).2+0≤_
          omega
      | pair head tail =>
          obtain ⟨bit,seenHead,next,headFee⟩ := seen_andThen _ _ followed
          obtain ⟨seen,seenTail,_,tailFee⟩ := seen_andThen _ _ next
          have firstBit := flag_paid size fits bounded.1 seenHead
          have remaining := ih bounded.2 seenTail
          rw [headFee,tailFee]
          change (fetch s address).2+((flag s head).2+((word s fuel tail).2+0))≤_
          omega

end DirectedFlowCutGap.CachedWordRead
