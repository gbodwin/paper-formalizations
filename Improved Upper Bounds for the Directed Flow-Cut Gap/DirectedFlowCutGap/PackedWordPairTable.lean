import DirectedFlowCutGap.WordPairTableRead

/-!
# A charged Boolean/list constructor for stored two-word rows

Every allocation executes `appendCell`, an actual `copyBits` of the returned
address, and binary `increment true`. The old physical heap and fresh cell are
copied by the existing closed append execution certificate. Immutable local
aliases retain earlier roots; copying their bits into cells is paid by append.
Each allocation also pays 32 for local tuple/record construction and the caller's
list-case/recursion bookkeeping. The empty table is itself an allocated nil.
No natural decoding computes an address: `value` occurs only in specifications.
Exact stored digit order and all padding are preserved, in one append-only heap.

This certifies these concrete Boolean/list bodies and declared primitive
charges, not compilation of this constructor into the finite instruction
language, native host allocation time, input acquisition, or substitution into
the whole graph oracle. It does not change the graph-level read charge.
-/
namespace DirectedFlowCutGap.PackedWordPairTable
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

structure Prepared where
  heap : Heap
  next : Bits
  root : Bits
  operations : ℕ
  deriving Repr

/-- One paid allocation; all output addresses come from the binary cursor. -/
def allocate (c : Cell Bits) (s : Prepared) : Prepared :=
  let h := appendCell s.heap c
  let r := EncodedSequenceAccess.copyBits s.next
  let n := increment true s.next
  ⟨h.1, n.1, r.1, s.operations + h.2 + r.2 + n.2 + 32⟩

def empty : Prepared := ⟨[], [], [], 0⟩
def seed : Prepared := allocate .nil empty

/-- Tail-first construction retains the exact incoming Boolean list. -/
def word : Bits → Prepared → Prepared
  | [], s => allocate .nil s
  | b :: bs, s =>
      let t := word bs s
      let f := allocate (.flag b) t
      allocate (.pair f.root t.root) f

/-- Build both padded words, then the record and the outer list spine. -/
def prepend (row : Bits × Bits) (s : Prepared) : Prepared :=
  let n := word row.1 s
  let d := word row.2 n
  let p := allocate (.pair n.root d.root) d
  allocate (.pair p.root s.root) p

def construct : List (Bits × Bits) → Prepared
  | [] => seed
  | row :: rows => prepend row (construct rows)

/-- Closed evidence for every allocated cell and every copied address. The
increment is the literal existing Boolean ripple-carry body. -/
theorem allocate_exec (c : Cell Bits) (s : Prepared) :
    AppendCellExec s.heap c (allocate c s).heap (appendCell s.heap c).2 ∧
    EncodedSequenceAccess.BitsCopyExec s.next (allocate c s).root
      (EncodedSequenceAccess.copyBits s.next).2 ∧
    (allocate c s).next = (increment true s.next).1 ∧
    (allocate c s).operations = s.operations + (appendCell s.heap c).2 +
      (EncodedSequenceAccess.copyBits s.next).2 + (increment true s.next).2 + 32 := by
  exact ⟨appendCell_exec _ _, EncodedSequenceAccess.copyBits_exec _, rfl, rfl⟩

@[simp] theorem allocate_heap (c : Cell Bits) (s : Prepared) :
    (allocate c s).heap = s.heap ++ [c] := appendCell_value _ _

@[simp] theorem allocate_root (c : Cell Bits) (s : Prepared) :
    (allocate c s).root = s.next := copiedWord _

@[simp] theorem allocate_length (c : Cell Bits) (s : Prepared) :
    (allocate c s).heap.length = s.heap.length + 1 := by simp

/-- Literal append-only preservation, with no expansion of shared references. -/
def Extends (h k : Heap) : Prop := ∃ extra, k = h ++ extra

theorem Extends.refl (h : Heap) : Extends h h := ⟨[], by simp⟩

theorem Extends.trans {h k l : Heap} (a : Extends h k) (b : Extends k l) :
    Extends h l := by
  obtain ⟨u, rfl⟩ := a
  obtain ⟨v, rfl⟩ := b
  exact ⟨u ++ v, by simp [List.append_assoc]⟩

theorem Extends.length_le {h k : Heap} (a : Extends h k) : h.length ≤ k.length := by
  obtain ⟨extra, rfl⟩ := a
  simp

theorem allocate_extends (c : Cell Bits) (s : Prepared) :
    Extends s.heap (allocate c s).heap := ⟨[c], allocate_heap _ _⟩

theorem Extends.lookup {h k : Heap} (a : Extends h k) {r : ℕ} {c : Cell ℕ}
    (hc : (eraseHeap h)[r]? = some c) : (eraseHeap k)[r]? = some c := by
  obtain ⟨extra, rfl⟩ := a
  rw [eraseHeap_append]
  exact lookup_extend hc _

theorem Extends.word {h k : Heap} (a : Extends h k) {r : ℕ} {bs : Bits}
    (hb : BoolList (eraseHeap h) r bs) : BoolList (eraseHeap k) r bs := by
  obtain ⟨extra, rfl⟩ := a
  rw [eraseHeap_append]
  exact boolList_extend hb _

theorem table_extend {h : NaturalHeap} {r : ℕ} {rows : List (Bits × Bits)}
    (ht : WordPairTableRead.Table h r rows) (extra : NaturalHeap) :
    WordPairTableRead.Table (h ++ extra) r rows := by
  induction ht with
  | nil hn => exact .nil (lookup_extend hn extra)
  | cons hp hi hn hd _ ih =>
      exact .cons (lookup_extend hp extra) (lookup_extend hi extra)
        (boolList_extend hn extra) (boolList_extend hd extra) ih

theorem Extends.table {h k : Heap} (a : Extends h k) {r : ℕ}
    {rows : List (Bits × Bits)} (ht : WordPairTableRead.Table (eraseHeap h) r rows) :
    WordPairTableRead.Table (eraseHeap k) r rows := by
  obtain ⟨extra, rfl⟩ := a
  rw [eraseHeap_append]
  exact table_extend ht _

/-- The cubic potential pays all previously executed primitive calls. -/
structure StateBound (s : Prepared) : Prop where
  next_value : value s.next = s.heap.length
  next_width : s.next.length ≤ s.heap.length
  root_width : s.root.length ≤ s.heap.length
  heap_bound : s.heap.Bounded s.heap.length
  charge : s.operations ≤ 64 * s.heap.length ^ 3

theorem empty_bound : StateBound empty := by
  refine ⟨rfl, by simp [empty], by simp [empty], ?_, by simp [empty]⟩
  simp [empty, Heap.Bounded]

theorem allocate_charge {s : Prepared} (h : StateBound s) {c : Cell Bits}
    (hc : c.Bounded s.heap.length) :
    (allocate c s).operations ≤ s.operations + 64 * (s.heap.length + 1)^2 := by
  have ha := appendCell_bound h.heap_bound hc
  have hi := (increment_spec true s.next).2.2
  have hw := h.next_width
  simp only [allocate, copiedWordCost]
  nlinarith

theorem allocate_bound {s : Prepared} (h : StateBound s) {c : Cell Bits}
    (hc : c.Bounded s.heap.length) : StateBound (allocate c s) := by
  have hi := increment_spec true s.next
  have charge := allocate_charge h hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [allocate_length]
    change value (increment true s.next).1 = s.heap.length + 1
    simpa [h.next_value] using hi.1
  · rw [allocate_length]
    change (increment true s.next).1.length ≤ s.heap.length + 1
    exact hi.2.1.trans (Nat.add_le_add_right h.next_width 1)
  · simpa using h.next_width.trans (Nat.le_succ _)
  · rw [allocate_heap]
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact heapBound_mono h.heap_bound (by simp) d hd
    · have eq : d = c := by simpa using hd
      subst d
      cases c with
      | nil => trivial
      | flag _ => trivial
      | pair a b => exact ⟨hc.1.trans (by simp), hc.2.trans (by simp)⟩
  · rw [allocate_length]
    have := h.charge
    nlinarith [sq_nonneg (s.heap.length : ℤ)]

theorem allocate_lookup {s : Prepared} (h : StateBound s) (c : Cell Bits) :
    (eraseHeap (allocate c s).heap)[value (allocate c s).root]? = some (eraseCell c) := by
  simp only [allocate_heap, allocate_root, h.next_value, eraseHeap_append]
  have length : (eraseHeap s.heap).length = s.heap.length := by simp [eraseHeap]
  rw [List.getElem?_append_right (by omega), length]
  simp [eraseHeap]

structure WordResult (s : Prepared) (bs : Bits) (out : Prepared) : Prop where
  bound : StateBound out
  length : out.heap.length = s.heap.length + 1 + 2 * bs.length
  extension : Extends s.heap out.heap
  representation : BoolList (eraseHeap out.heap) (value out.root) bs

theorem word_spec (bs : Bits) {s : Prepared} (hs : StateBound s) :
    WordResult s bs (word bs s) := by
  induction bs with
  | nil =>
      refine ⟨allocate_bound hs (by trivial), ?_, allocate_extends _ _, ?_⟩
      · simp [word]
      · exact .nil (allocate_lookup hs .nil)
  | cons b bs ih =>
      let t := word bs s
      let f := allocate (.flag b) t
      have ht : StateBound t := ih.bound
      have hf : StateBound f := allocate_bound ht (by trivial)
      have ef : Extends t.heap f.heap := allocate_extends _ _
      have pairBound : (Cell.pair f.root t.root).Bounded f.heap.length :=
        ⟨hf.root_width, ht.root_width.trans ef.length_le⟩
      have ep := allocate_extends (.pair f.root t.root) f
      refine ⟨allocate_bound hf pairBound, ?_, ih.extension.trans (ef.trans ep), ?_⟩
      · change (allocate (.pair f.root t.root) f).heap.length = _
        simp only [allocate_length]
        have flen : f.heap.length = t.heap.length + 1 := allocate_length _ _
        have tlen := ih.length
        change t.heap.length = _ at tlen
        simp only [List.length_cons]
        omega
      · change BoolList (eraseHeap (allocate (.pair f.root t.root) f).heap)
          (value (allocate (.pair f.root t.root) f).root) (b :: bs)
        apply BoolList.cons (allocate_lookup hf (.pair f.root t.root))
        · exact ep.lookup (allocate_lookup ht (.flag b))
        · exact (ef.trans ep).word ih.representation

def storedBits (rows : List (Bits × Bits)) : ℕ :=
  (rows.map (fun row => row.1.length + row.2.length)).sum

@[simp] theorem storedBits_nil : storedBits [] = 0 := rfl
@[simp] theorem storedBits_cons (row : Bits × Bits) (rows : List (Bits × Bits)) :
    storedBits (row :: rows) = row.1.length + row.2.length + storedBits rows := by
  simp [storedBits]

structure TableResult (rows : List (Bits × Bits)) (s : Prepared) : Prop where
  bound : StateBound s
  length : s.heap.length = 1 + 4 * rows.length + 2 * storedBits rows
  representation : WordPairTableRead.Table (eraseHeap s.heap) (value s.root) rows

theorem seed_spec : TableResult [] seed := by
  refine ⟨allocate_bound empty_bound (by trivial), ?_, ?_⟩
  · simp [seed, empty]
  · exact .nil (allocate_lookup empty_bound .nil)

theorem prepend_spec {rows : List (Bits × Bits)} {s : Prepared}
    (hs : TableResult rows s) (row : Bits × Bits) :
    TableResult (row :: rows) (prepend row s) := by
  let n := word row.1 s
  let d := word row.2 n
  let p := allocate (.pair n.root d.root) d
  have hn : WordResult s row.1 n := word_spec row.1 hs.bound
  have hd : WordResult n row.2 d := word_spec row.2 hn.bound
  have pairBound : (Cell.pair n.root d.root).Bounded d.heap.length :=
    ⟨hn.bound.root_width.trans hd.extension.length_le, hd.bound.root_width⟩
  have hp : StateBound p := allocate_bound hd.bound pairBound
  have ep : Extends d.heap p.heap := allocate_extends _ _
  have es : Extends s.heap p.heap := hn.extension.trans (hd.extension.trans ep)
  have spineBound : (Cell.pair p.root s.root).Bounded p.heap.length :=
    ⟨hp.root_width, hs.bound.root_width.trans es.length_le⟩
  have eq := allocate_extends (.pair p.root s.root) p
  refine ⟨allocate_bound hp spineBound, ?_, ?_⟩
  · change (allocate (.pair p.root s.root) p).heap.length = _
    rw [allocate_length]
    have plen : p.heap.length = d.heap.length + 1 := allocate_length _ _
    have hnl := hn.length
    have hdl := hd.length
    have hsl := hs.length
    simp only [List.length_cons, storedBits_cons]
    omega
  · change WordPairTableRead.Table
      (eraseHeap (allocate (.pair p.root s.root) p).heap)
      (value (allocate (.pair p.root s.root) p).root) (row :: rows)
    apply WordPairTableRead.Table.cons (allocate_lookup hp (.pair p.root s.root))
      (eq.lookup (allocate_lookup hd.bound (.pair n.root d.root)))
    · exact (hd.extension.trans (ep.trans eq)).word hn.representation
    · exact (ep.trans eq).word hd.representation
    · exact (es.trans eq).table hs.representation

theorem construct_valid (rows : List (Bits × Bits)) : TableResult rows (construct rows) := by
  induction rows with
  | nil => exact seed_spec
  | cons row rows ih => exact prepend_spec ih row

/-- An explicit universal cubic bound in row count plus all stored bits. -/
theorem construct_charge (rows : List (Bits × Bits)) :
    (construct rows).operations ≤ 4096 * (rows.length + storedBits rows + 1)^3 := by
  have h := construct_valid rows
  have small : (construct rows).heap.length ≤ 4 * (rows.length + storedBits rows + 1) := by
    rw [h.length]
    omega
  calc
    (construct rows).operations ≤ 64 * (construct rows).heap.length^3 := h.bound.charge
    _ ≤ 64 * (4 * (rows.length + storedBits rows + 1))^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 3)
    _ = _ := by ring

/-- Exact storage, dense cursor, same-heap row representation, width bounds,
physical reference-word boundedness, and the complete declared charge. -/
theorem construct_spec (rows : List (Bits × Bits)) :
    (construct rows).heap.length = 1 + 4 * rows.length + 2 * storedBits rows ∧
    value (construct rows).next = (construct rows).heap.length ∧
    WordPairTableRead.Table (eraseHeap (construct rows).heap)
      (value (construct rows).root) rows ∧
    (construct rows).next.length ≤ 4 * (rows.length + storedBits rows) + 1 ∧
    (construct rows).root.length ≤ 4 * (rows.length + storedBits rows) + 1 ∧
    (construct rows).heap.Bounded (4 * (rows.length + storedBits rows) + 1) ∧
    (construct rows).operations ≤ 4096 * (rows.length + storedBits rows + 1)^3 := by
  have h := construct_valid rows
  have size : (construct rows).heap.length ≤ 4 * (rows.length + storedBits rows) + 1 := by
    rw [h.length]
    omega
  exact ⟨h.length, h.bound.next_value, h.representation,
    h.bound.next_width.trans size, h.bound.root_width.trans size,
    heapBound_mono h.bound.heap_bound size, construct_charge rows⟩

end DirectedFlowCutGap.PackedWordPairTable
