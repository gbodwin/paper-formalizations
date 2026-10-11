import DirectedFlowCutGap.BooleanTableRead

/-!
# Charged construction of a packed Boolean-list heap

The executable constructor uses two literal full-copy `appendCell` calls and
 two binary `increment true` calls per input bit, processed from the tail.
Natural values and lengths appear only in specifications and ghost charges.
The one-cell seed costs 5; each cons has a fixed list/record allowance of 12.
All suffix spines already occur in this same heap; no unary index heap is built.
This component does not charge acquisition/encoding of the incoming Boolean
list or index word, and does not substitute the graph-level controller.
-/
namespace DirectedFlowCutGap.PackedBooleanConstructor
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

structure Prepared where
  heap : Heap
  next : Bits
  root : Bits
  operations : ℕ
  deriving Repr

def seed : Prepared := ⟨[.nil], [true], [], 5⟩

/-- The addresses come only from the maintained binary cursor. -/
def prepend (b : Bool) (s : Prepared) : Prepared :=
  let flag := appendCell s.heap (.flag b)
  let pairAddress := increment true s.next
  let pair := appendCell flag.1 (.pair s.next s.root)
  let next := increment true pairAddress.1
  ⟨pair.1, next.1, pairAddress.1,
    s.operations + flag.2 + pairAddress.2 + pair.2 + next.2 + 12⟩

def construct : List Bool → Prepared
  | [] => seed
  | b :: bs => prepend b (construct bs)

/-- Closed per-cons execution evidence exposes both paid physical appends. -/
theorem prepend_exec (b : Bool) (s : Prepared) :
    AppendCellExec s.heap (.flag b)
      (appendCell s.heap (.flag b)).1 (appendCell s.heap (.flag b)).2 ∧
    AppendCellExec (appendCell s.heap (.flag b)).1 (.pair s.next s.root)
      (prepend b s).heap
      (appendCell (appendCell s.heap (.flag b)).1 (.pair s.next s.root)).2 ∧
    (prepend b s).root = (increment true s.next).1 ∧
    (prepend b s).next = (increment true (increment true s.next).1).1 ∧
    (prepend b s).operations = s.operations + (appendCell s.heap (.flag b)).2 +
      (increment true s.next).2 +
      (appendCell (appendCell s.heap (.flag b)).1 (.pair s.next s.root)).2 +
      (increment true (increment true s.next).1).2 + 12 := by
  exact ⟨appendCell_exec _ _, appendCell_exec _ _, rfl, rfl, rfl⟩

@[simp] theorem prepend_heap (b : Bool) (s : Prepared) :
    (prepend b s).heap = s.heap ++ [.flag b, .pair s.next s.root] := by
  simp [prepend, appendCell_value, List.append_assoc]

@[simp] theorem eraseHeap_append (h k : Heap) :
    eraseHeap (h ++ k) = eraseHeap h ++ eraseHeap k := by
  simp [eraseHeap]

theorem lookup_extend {h : NaturalHeap} {a : ℕ} {c : Cell ℕ}
    (hc : h[a]? = some c) (k : NaturalHeap) : (h ++ k)[a]? = some c := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).choose]
  exact hc

theorem boolList_extend {h : NaturalHeap} {a : ℕ} {xs : List Bool}
    (rep : BoolList h a xs) (k : NaturalHeap) : BoolList (h ++ k) a xs := by
  induction rep with
  | nil hn => exact .nil (lookup_extend hn k)
  | cons hp hb _ ih => exact .cons (lookup_extend hp k) (lookup_extend hb k) ih

theorem indexSpine_extend {h : NaturalHeap} {a n : ℕ}
    (rep : IndexSpine h a n) (k : NaturalHeap) : IndexSpine (h ++ k) a n := by
  induction rep with
  | nil hn => exact .nil (lookup_extend hn k)
  | cons hp _ ih => exact .cons (lookup_extend hp k) ih

theorem boolList_spine {h : NaturalHeap} {a : ℕ} {xs : List Bool}
    (rep : BoolList h a xs) : IndexSpine h a xs.length := by
  induction rep with
  | nil hn => exact .nil hn
  | cons hp _ _ ih => exact .cons hp ih

theorem heapBound_mono {h : Heap} {B C : ℕ}
    (hh : h.Bounded B) (hBC : B ≤ C) : h.Bounded C := by
  intro c hc
  have hb := hh c hc
  cases c with
  | nil => trivial
  | flag _ => trivial
  | pair _ _ => exact ⟨hb.1.trans hBC, hb.2.trans hBC⟩

/-- All addresses have a deliberately coarse linear width bound. -/
structure Valid (xs : List Bool) (s : Prepared) : Prop where
  heap_length : s.heap.length = 2 * xs.length + 1
  next_value : value s.next = 2 * xs.length + 1
  root_value : value s.root = 2 * xs.length
  next_width : s.next.length ≤ 2 * xs.length + 1
  root_width : s.root.length ≤ 2 * xs.length + 1
  heap_bound : s.heap.Bounded (2 * xs.length + 1)
  table : BoolList (eraseHeap s.heap) (value s.root) xs
  suffix : ∀ i, i ≤ xs.length → IndexSpine (eraseHeap s.heap) (2 * i) i

private theorem seed_valid : Valid [] seed := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, ?_, ?_, ?_⟩
  · simp [seed, Heap.Bounded, Cell.Bounded]
  · exact .nil rfl
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    exact .nil rfl

private theorem prepend_valid {xs : List Bool} {s : Prepared}
    (h : Valid xs s) (b : Bool) : Valid (b :: xs) (prepend b s) := by
  have inc₁ := increment_spec true s.next
  have inc₂ := increment_spec true (increment true s.next).1
  have heapEq : eraseHeap (prepend b s).heap = eraseHeap s.heap ++
      [.flag b, .pair (2 * xs.length + 1) (2 * xs.length)] := by
    simp [prepend_heap, eraseHeap, eraseCell, Cell.map, h.next_value, h.root_value]
  have oldLength : (eraseHeap s.heap).length = 2 * xs.length + 1 := by
    simpa [eraseHeap] using h.heap_length
  have flagAt : (eraseHeap (prepend b s).heap)[2 * xs.length + 1]? = some (.flag b) := by
    rw [heapEq, List.getElem?_append_right (by omega), oldLength]
    simp
  have pairAt : (eraseHeap (prepend b s).heap)[2 * xs.length + 2]? =
      some (.pair (2 * xs.length + 1) (2 * xs.length)) := by
    rw [heapEq, List.getElem?_append_right (by omega), oldLength]
    have : 2 * xs.length + 2 - (2 * xs.length + 1) = 1 := by omega
    simp [this]
  have rootVal : value (prepend b s).root = 2 * xs.length + 2 := by
    simpa [prepend, h.next_value] using inc₁.1
  have table : BoolList (eraseHeap (prepend b s).heap)
      (value (prepend b s).root) (b :: xs) := by
    rw [rootVal]
    apply BoolList.cons pairAt flagAt
    rw [heapEq, ← h.root_value]
    exact boolList_extend h.table _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, table, ?_⟩
  · simp [h.heap_length, Nat.mul_add, Nat.add_assoc]
  · have hn := h.next_value
    simp only [prepend, List.length_cons, Bool.toNat_true] at inc₁ inc₂ ⊢
    omega
  · simp only [List.length_cons]
    omega
  · simp only [prepend, List.length_cons] at inc₁ inc₂ ⊢
    have := h.next_width
    omega
  · simp only [prepend, List.length_cons] at inc₁ ⊢
    have := h.next_width
    omega
  · intro c hc
    rw [prepend_heap] at hc
    rcases List.mem_append.mp hc with old | fresh
    · exact heapBound_mono h.heap_bound (by simp only [List.length_cons]; omega) c old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · trivial
      · exact ⟨h.next_width.trans (by simp only [List.length_cons]; omega), h.root_width.trans (by simp only [List.length_cons]; omega)⟩
  · intro i hi
    by_cases old : i ≤ xs.length
    · rw [heapEq]
      exact indexSpine_extend (h.suffix i old) _
    · have eq : i = (b :: xs).length := by simp only [List.length_cons] at *; omega
      subst i
      have spine := boolList_spine table
      simpa only [List.length_cons, rootVal, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using spine

theorem construct_valid (xs : List Bool) : Valid xs (construct xs) := by
  induction xs with
  | nil => exact seed_valid
  | cons b bs ih => exact prepend_valid ih b

/-- Each charged cons is at most quadratic in the current number of entries. -/
theorem prepend_charge {xs : List Bool} {s : Prepared} (h : Valid xs s) (b : Bool) :
    (prepend b s).operations ≤ s.operations + 160 * (xs.length + 1)^2 := by
  have flagBound : (Cell.flag b : Cell Bits).Bounded (2 * xs.length + 1) := trivial
  have flagHeapBound : ((appendCell s.heap (.flag b)).1).Bounded (2 * xs.length + 1) := by
    rw [appendCell_value]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.heap_bound c hc
    · have eq : c = .flag b := by simpa using hc
      simpa [eq] using flagBound
  have pairBound : (Cell.pair s.next s.root).Bounded (2 * xs.length + 1) :=
    ⟨h.next_width, h.root_width⟩
  have flagCost := appendCell_bound h.heap_bound flagBound
  have pairCost := appendCell_bound flagHeapBound pairBound
  have inc₁ := increment_spec true s.next
  have inc₂ := increment_spec true (increment true s.next).1
  simp only [appendCell_value, List.length_append, List.length_singleton, h.heap_length] at flagCost pairCost
  have nw := h.next_width
  simp only [prepend, appendCell_value]
  nlinarith [inc₁.2.1, inc₁.2.2, inc₂.2.2]

/-- Explicit polynomial preparation charge, including both paid copies. -/
theorem construct_charge (xs : List Bool) :
    (construct xs).operations ≤ 128 * (xs.length + 1)^3 := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
      have hs := prepend_charge (construct_valid bs) b
      simp only [construct, List.length_cons]
      nlinarith

/-- Combined output theorem: actual storage, cursor, root, widths, and charge. -/
theorem construct_spec (xs : List Bool) :
    (construct xs).heap.length = 2 * xs.length + 1 ∧
    value (construct xs).next = (construct xs).heap.length ∧
    value (construct xs).root = 2 * xs.length ∧
    BoolList (eraseHeap (construct xs).heap) (value (construct xs).root) xs ∧
    (∀ i, i ≤ xs.length → IndexSpine (eraseHeap (construct xs).heap) (2 * i) i) ∧
    (construct xs).next.length ≤ 2 * xs.length + 1 ∧
    (construct xs).root.length ≤ 2 * xs.length + 1 ∧
    (construct xs).heap.Bounded (2 * xs.length + 1) ∧
    (construct xs).operations ≤ 128 * (xs.length + 1)^3 := by
  have h := construct_valid xs
  exact ⟨h.heap_length, h.next_value.trans h.heap_length.symm, h.root_value,
    h.table, h.suffix, h.next_width, h.root_width, h.heap_bound, construct_charge xs⟩

end DirectedFlowCutGap.PackedBooleanConstructor
