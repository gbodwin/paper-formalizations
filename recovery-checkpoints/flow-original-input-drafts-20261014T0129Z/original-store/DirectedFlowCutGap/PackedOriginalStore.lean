import DirectedFlowCutGap.PackedWordPairTable
import DirectedFlowCutGap.OriginalStoreInputViews

/-!
UNVERIFIED ADDITIVE DRAFT, 2026-10-14. No Lean compilation has been run.

Construct cost, adjacency and demand roots in one append-only physical heap.
The allocation/copy/increment bodies and cubic potential are the published
PackedWordPairTable ones. Constructors retain the exact input words, including
all rational padding. Natural demand addresses below are specification-only.
This is Boolean/list certification, NOT a finite-instruction parser, host-time
claim, or whole-paper theorem.
-/
namespace DirectedFlowCutGap.PackedOriginalStore
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor BinaryPointerListRead
open PackedWordPairTable

/-- A word-pair table appended to any already constructed bounded heap. -/
def tableInto : List (Bits × Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | row::rows,s => PackedWordPairTable.prepend row (tableInto rows s)

structure TableAppendResult (rows : List (Bits × Bits))
    (s out : PackedWordPairTable.Prepared) : Prop where
  bound : StateBound out
  length : out.heap.length=s.heap.length+1+4*rows.length+2*storedBits rows
  extension : Extends s.heap out.heap
  representation : WordPairTableRead.Table (eraseHeap out.heap) (value out.root) rows

/-- The published prepend body is reused literally; only its origin-relative
length invariant and append-only witness are generalized. -/
theorem prepend_into_spec {rows : List (Bits × Bits)}
    {base s : PackedWordPairTable.Prepared} (hs : TableAppendResult rows base s)
    (row : Bits × Bits) :
    TableAppendResult (row::rows) base (PackedWordPairTable.prepend row s) := by
  let n := word row.1 s
  let d := word row.2 n
  let p := PackedWordPairTable.allocate (.pair n.root d.root) d
  have hn : WordResult s row.1 n := word_spec row.1 hs.bound
  have hd : WordResult n row.2 d := word_spec row.2 hn.bound
  have bp : (Cell.pair n.root d.root).Bounded d.heap.length :=
    ⟨hn.bound.root_width.trans hd.extension.length_le,hd.bound.root_width⟩
  have hp : StateBound p := allocate_bound hd.bound bp
  have ep : Extends d.heap p.heap := allocate_extends _ _
  have es : Extends s.heap p.heap := hn.extension.trans (hd.extension.trans ep)
  have bq : (Cell.pair p.root s.root).Bounded p.heap.length :=
    ⟨hp.root_width,hs.bound.root_width.trans es.length_le⟩
  have eq := allocate_extends (.pair p.root s.root) p
  refine ⟨allocate_bound hp bq,?_,hs.extension.trans (es.trans eq),?_⟩
  · change (PackedWordPairTable.allocate (.pair p.root s.root) p).heap.length=_
    rw [allocate_length]
    have plen : p.heap.length=d.heap.length+1 := allocate_length _ _
    have hnl := hn.length
    have hdl := hd.length
    have hsl := hs.length
    simp only [List.length_cons,storedBits_cons]
    omega
  · change WordPairTableRead.Table
      (eraseHeap (PackedWordPairTable.allocate (.pair p.root s.root) p).heap)
      (value (PackedWordPairTable.allocate (.pair p.root s.root) p).root) (row::rows)
    apply WordPairTableRead.Table.cons (allocate_lookup hp (.pair p.root s.root))
      (eq.lookup (allocate_lookup hd.bound (.pair n.root d.root)))
    · exact (hd.extension.trans (ep.trans eq)).word hn.representation
    · exact (ep.trans eq).word hd.representation
    · exact (es.trans eq).table hs.representation

theorem tableInto_spec (rows : List (Bits × Bits))
    {s : PackedWordPairTable.Prepared} (hs : StateBound s) :
    TableAppendResult rows s (tableInto rows s) := by
  induction rows with
  | nil =>
      refine ⟨allocate_bound hs (by trivial),?_,allocate_extends _ _,?_⟩
      · simp [tableInto]
      · exact .nil (allocate_lookup hs .nil)
  | cons row rows ih => exact prepend_into_spec ih row

def rowBits (rows : List Bits) : ℕ := (rows.map List.length).sum

/-- A matrix needs a list of word roots, not two-word records. -/
def matrixInto : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | row::rows,s =>
      let t := matrixInto rows s
      let w := word row t
      PackedWordPairTable.allocate (.pair w.root t.root) w

theorem matrix_cons {h : NaturalHeap} {root head tail : ℕ} {row : Bits} {rows : List Bits}
    (hp : h[root]?=some (.pair head tail)) (hw : BoolList h head row)
    (ht : GraphAdjacencyProgram.Matrix h tail rows) :
    GraphAdjacencyProgram.Matrix h root (row::rows) := by
  obtain ⟨roots,hl,hr,hrows⟩ := ht
  refine ⟨head::roots,by simpa using hl,PointerList.cons hp hr,?_⟩
  intro i hi
  cases i with
  | zero => exact hw
  | succ i => simpa using hrows i (by simpa using hi)

theorem extends_matrix {h k : Heap} (e : Extends h k) {r : ℕ} {rows : List Bits}
    (hm : GraphAdjacencyProgram.Matrix (eraseHeap h) r rows) :
    GraphAdjacencyProgram.Matrix (eraseHeap k) r rows := by
  obtain ⟨extra,rfl⟩ := e
  rw [eraseHeap_append]
  exact GraphAdjacencyProgram.matrix_extend hm _

structure MatrixAppendResult (rows : List Bits)
    (s out : PackedWordPairTable.Prepared) : Prop where
  bound : StateBound out
  length : out.heap.length=s.heap.length+1+2*rows.length+2*rowBits rows
  extension : Extends s.heap out.heap
  representation : GraphAdjacencyProgram.Matrix (eraseHeap out.heap) (value out.root) rows

theorem matrixInto_spec (rows : List Bits)
    {s : PackedWordPairTable.Prepared} (hs : StateBound s) :
    MatrixAppendResult rows s (matrixInto rows s) := by
  induction rows with
  | nil =>
      refine ⟨allocate_bound hs (by trivial),?_,allocate_extends _ _,?_⟩
      · simp [matrixInto,rowBits]
      · exact ⟨[],rfl,PointerList.nil (allocate_lookup hs .nil),by simp⟩
  | cons row rows ih =>
      let t := matrixInto rows s
      let w := word row t
      have hw : WordResult t row w := word_spec row ih.bound
      have bp : (Cell.pair w.root t.root).Bounded w.heap.length :=
        ⟨hw.bound.root_width,ih.bound.root_width.trans hw.extension.length_le⟩
      have ep := allocate_extends (.pair w.root t.root) w
      refine ⟨allocate_bound hw.bound bp,?_,ih.extension.trans (hw.extension.trans ep),?_⟩
      · change (PackedWordPairTable.allocate (.pair w.root t.root) w).heap.length=_
        rw [allocate_length]
        have ht := ih.length
        have hl := hw.length
        simp only [rowBits,List.map_cons,List.sum_cons,List.length_cons] at *
        omega
      · exact matrix_cons (allocate_lookup hw.bound (.pair w.root t.root))
          (ep.word hw.representation)
          (extends_matrix (hw.extension.trans ep) ih.representation)

/-- This is a proof-only conversion. Original demand occurrence and record
addresses are witnesses read from the represented table; no constructor calls
`value` to manufacture an address. Repeated demands retain their separate
positions in the represented list; this theorem does not state address Nodup. -/
theorem table_demands {n : ℕ} (label : Fin n → Bits)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) {h : NaturalHeap} {root : ℕ}
    (ht : WordPairTableRead.Table h root (ds.map fun d => (label d.1,label d.2))) :
    ∃ xs,DemandCollection.DemandList h root xs ∧
      List.Forall₂ (DemandCollection.EncodesDemand label) xs ds := by
  induction ds generalizing root with
  | nil =>
      cases ht with
      | nil hp => exact ⟨[],.nil hp,.nil⟩
  | cons d ds ih =>
      cases ht with
      | @cons root item tail num den a b rest hp hi hn hd hr =>
          obtain ⟨xs,hxs,encoded⟩ := ih hr
          let x : DemandCollection.Demand := ⟨label d.1,label d.2,item,root⟩
          exact ⟨x::xs,.cons rfl hp ⟨num,den,hi,hn,hd⟩ hxs,
            .cons ⟨rfl,rfl⟩ encoded⟩

structure Store where
  prepared : PackedWordPairTable.Prepared
  costRoot : Bits
  matrixRoot : Bits

/-- Three constructor passes, one physical heap, no address relocation. -/
def construct (costs : List (Bits × Bits)) (matrix : List Bits)
    (demands : List (Bits × Bits)) : Store :=
  let c := PackedWordPairTable.construct costs
  let m := matrixInto matrix c
  let d := tableInto demands m
  ⟨d,c.root,m.root⟩

def cells (costs : List (Bits × Bits)) (matrix : List Bits)
    (demands : List (Bits × Bits)) : ℕ :=
  3+4*costs.length+2*storedBits costs+
    2*matrix.length+2*rowBits matrix+4*demands.length+2*storedBits demands

structure StoreResult (costs : List (Bits × Bits)) (matrix : List Bits)
    (demands : List (Bits × Bits)) (s : Store) : Prop where
  bound : StateBound s.prepared
  length : s.prepared.heap.length=cells costs matrix demands
  cost_width : s.costRoot.length ≤ s.prepared.heap.length
  matrix_width : s.matrixRoot.length ≤ s.prepared.heap.length
  cost_table : WordPairTableRead.Table (eraseHeap s.prepared.heap) (value s.costRoot) costs
  matrix_table : GraphAdjacencyProgram.Matrix (eraseHeap s.prepared.heap) (value s.matrixRoot) matrix
  demand_table : WordPairTableRead.Table (eraseHeap s.prepared.heap) (value s.prepared.root) demands

theorem construct_spec (costs : List (Bits × Bits)) (matrix : List Bits)
    (demands : List (Bits × Bits)) : StoreResult costs matrix demands (construct costs matrix demands) := by
  have hc := PackedWordPairTable.construct_valid costs
  have hm := matrixInto_spec matrix hc.bound
  have hd := tableInto_spec demands hm.bound
  refine ⟨hd.bound,?_,?_,?_,?_,?_,hd.representation⟩
  · change (tableInto demands (matrixInto matrix (PackedWordPairTable.construct costs))).heap.length=_
    rw [hd.length,hm.length,hc.length]
    simp only [cells]
    omega
  · exact hc.bound.root_width.trans (hm.extension.trans hd.extension).length_le
  · exact hm.bound.root_width.trans hd.extension.length_le
  · exact (hm.extension.trans hd.extension).table hc.representation
  · exact extends_matrix hd.extension hm.representation

/-- Paid register and cursor copies install the represented roots. The source
is empty, the stack is empty, and the fixed dispatcher entry is 13318. -/
def prepare (costs : List (Bits × Bits)) (matrix : List Bits)
    (demands : List (Bits × Bits)) : BitState 13320 × ℕ :=
  let s := construct costs matrix demands
  let regs := copyRegisters ⟨s.costRoot,s.matrixRoot,s.prepared.root,[]⟩
  let next := EncodedSequenceAccess.copyBits s.prepared.next
  (⟨s.prepared.heap,next.1,regs.1,[],13318,[]⟩,
    s.prepared.operations+regs.2+next.2+16)

/-- Explicit initial H/B: H counts all heap cells and the current state record;
B bounds every reference word. The source contains no uncharged input data. -/
theorem prepare_spec (costs : List (Bits × Bits)) (matrix : List Bits)
    (demands : List (Bits × Bits)) :
    let out := (prepare costs matrix demands).1
    let L := cells costs matrix demands
    out.Bounded (L+1) L ∧ out.pc=13318 ∧ out.stack=[] ∧ out.source=[] ∧
      value out.next=out.heap.length ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.a costs ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState out).registers.b matrix ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.c demands ∧
      (prepare costs matrix demands).2 ≤ 64*L^3+24*L+37 := by
  have h := construct_spec costs matrix demands
  have br : (Registers.mk (construct costs matrix demands).costRoot
      (construct costs matrix demands).matrixRoot
      (construct costs matrix demands).prepared.root ([] : Bits)).All
      (fun w => w.length ≤ cells costs matrix demands) := by
    refine ⟨h.cost_width.trans (by rw [h.length]),
      h.matrix_width.trans (by rw [h.length]),
      h.bound.root_width.trans (by rw [h.length]),by simp⟩
  have qr := copyRegisters_bound br
  have qn := h.bound.next_width
  have qc := h.bound.charge
  simp only [prepare,copyRegisters_value,copiedWord]
  refine ⟨?_,rfl,rfl,rfl,h.bound.next_value,h.cost_table,h.matrix_table,h.demand_table,?_⟩
  · simp only [State.Bounded,State.records,List.length_nil,Nat.add_zero]
    refine ⟨by rw [h.length],h.bound.next_width.trans (by rw [h.length]),
      heapBound_mono h.bound.heap_bound (by rw [h.length]),br,?_⟩
    simp
  · simp only [copiedWordCost]
    rw [h.length] at qn qc
    omega

end DirectedFlowCutGap.PackedOriginalStore
