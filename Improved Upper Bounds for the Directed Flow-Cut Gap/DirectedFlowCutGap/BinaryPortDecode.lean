import DirectedFlowCutGap.BinaryPortWeightPreparation
import DirectedFlowCutGap.EncodedRestrictedTestExec

/-!
# Literal binary permanent-port decoding and retained input cells

The three port blocks have their original size n, supplied as retained bits.
The decoder executes two fixed binary comparisons and, when needed, a fixed
binary subtraction. Doubling n is one zero-bit constructor. The core case
borrows the original padded label; the other two cases retain the actual
canonical subtraction result. No natural-number decoder runs in these bodies.

The two port callbacks then execute only fixed branches and the already
certified original adjacency or low-mask reads. Equality of a source and sink
uses the binary comparator; that true branch avoids the original cell read.
Closed execution rules list exactly these calls. Malformed reached reads
remain `none`, and unused malformed data is never inspected.

The low mask is the actual output of BinaryPortWeightPreparation. Original
weights and the exact query-cost fields are untouched. Representation maps
are observations of retained input, not free materialization. Finite label
enumeration, port matrix/mask construction, survivor/replica/chain assembly,
and global argument/frame movement remain separate enclosing-body joins.
The existing original-n/W envelope is not replaced by a bound in 3*n.
-/
namespace DirectedFlowCutGap.BinaryPortDecode
open BinaryArithmetic EncodedSequenceAccess
open EncodedRestrictedTestExec

inductive Kind where
  | core | source | sink
  deriving DecidableEq, Repr

structure PortCode where
  kind : Kind
  index : Bits
  deriving DecidableEq, Repr

/-- Only a mathematical observation of the already retained result. -/
def observe (p : PortCode) : Kind × ℕ := (p.kind,value p.index)

def observePort {n : ℕ} : EncodedPortPreparation.Port n → Kind × ℕ
  | .inl v => (.core,v.val)
  | .inr (.inl v) => (.source,v.val)
  | .inr (.inr v) => (.sink,v.val)

def twice (nBits : Bits) : Bits := false::nBits

@[simp] theorem twice_value (nBits : Bits) : value (twice nBits)=2*value nBits := by
  simp [twice,value]

/-- Valid Fin (3*n) labels need no additional range scan. For arbitrary words
this remains a total fixed body; only valid labels receive the finite-port theorem. -/
def decode (nBits label : Bits) : PortCode × ℕ :=
  let twoN := twice nBits
  let a := BinaryArithmetic.compare label nBits
  if a.less then (⟨.core,label⟩,a.steps+8) else
    let b := BinaryArithmetic.compare label twoN
    if b.less then
      let r := BinaryDivision.sub label nBits
      (⟨.source,r.1⟩,a.steps+b.steps+r.2+16)
    else
      let r := BinaryDivision.sub label twoN
      (⟨.sink,r.1⟩,a.steps+b.steps+r.2+16)

inductive DecodeExec (nBits label : Bits) : PortCode → ℕ → Prop
  | core : (BinaryArithmetic.compare label nBits).less=true →
      DecodeExec nBits label ⟨.core,label⟩ ((BinaryArithmetic.compare label nBits).steps+8)
  | source : (BinaryArithmetic.compare label nBits).less=false →
      (BinaryArithmetic.compare label (twice nBits)).less=true →
      DecodeExec nBits label ⟨.source,(BinaryDivision.sub label nBits).1⟩
        ((BinaryArithmetic.compare label nBits).steps+
          (BinaryArithmetic.compare label (twice nBits)).steps+
          (BinaryDivision.sub label nBits).2+16)
  | sink : (BinaryArithmetic.compare label nBits).less=false →
      (BinaryArithmetic.compare label (twice nBits)).less=false →
      DecodeExec nBits label ⟨.sink,(BinaryDivision.sub label (twice nBits)).1⟩
        ((BinaryArithmetic.compare label nBits).steps+
          (BinaryArithmetic.compare label (twice nBits)).steps+
          (BinaryDivision.sub label (twice nBits)).2+16)

theorem decode_exec (nBits label : Bits) :
    DecodeExec nBits label (decode nBits label).1 (decode nBits label).2 := by
  cases ha : (BinaryArithmetic.compare label nBits).less with
  | true => simpa only [decode,ha,ite_true] using DecodeExec.core ha
  | false =>
      cases hb : (BinaryArithmetic.compare label (twice nBits)).less with
      | true => simpa only [decode,ha,hb,Bool.false_eq_true,ite_false,ite_true] using
          DecodeExec.source ha hb
      | false => simpa only [decode,ha,hb,Bool.false_eq_true,ite_false] using
          DecodeExec.sink ha hb

theorem DecodeExec.result {nBits label : Bits} {p : PortCode} {q : ℕ}
    (h : DecodeExec nBits label p q) : p=(decode nBits label).1 ∧ q=(decode nBits label).2 := by
  cases h with
  | core ha => constructor <;> simp only [decode,ha,ite_true]
  | source ha hb => constructor <;> simp only [decode,ha,hb,Bool.false_eq_true,ite_false,ite_true]
  | sink ha hb => constructor <;> simp only [decode,ha,hb,Bool.false_eq_true,ite_false]

theorem decode_refines {n : ℕ} (nBits label : Bits) (hn : value nBits=n)
    (i : Fin (3*n)) (hi : value label=i.val) :
    observe (decode nBits label).1 = observePort (EncodedPortPreparation.decodePort i) := by
  have ha := (BinaryArithmetic.compare_spec label nBits).1
  have hb := (BinaryArithmetic.compare_spec label (twice nBits)).1
  have hs := (BinaryDivision.sub_spec label nBits).1
  have ht := (BinaryDivision.sub_spec label (twice nBits)).1
  rw [hn,hi] at ha hs
  rw [twice_value,hn,hi] at hb ht
  by_cases h : i.val<n
  · have he : (BinaryArithmetic.compare label nBits).less=true := ha.mpr h
    simp [decode,he,observe,hi,EncodedPortPreparation.decodePort,h,observePort]
  · have he : (BinaryArithmetic.compare label nBits).less=false :=
      Bool.eq_false_iff.mpr (fun hh => h (ha.mp hh))
    by_cases h' : i.val<2*n
    · have he' : (BinaryArithmetic.compare label (twice nBits)).less=true := hb.mpr h'
      simp [decode,he,he',observe,hs,EncodedPortPreparation.decodePort,h,h',observePort]
    · have he' : (BinaryArithmetic.compare label (twice nBits)).less=false :=
        Bool.eq_false_iff.mpr (fun hh => h' (hb.mp hh))
      simp [decode,he,he',observe,ht,EncodedPortPreparation.decodePort,h,h',observePort]

private theorem sub_length (xs ys : Bits) : (BinaryDivision.sub xs ys).1.length ≤ xs.length := by
  rw [(BinaryDivision.sub_spec xs ys).2.1]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.size_le.mpr (value_lt xs))

/-- A padded core label is retained unchanged; subtraction never increases width. -/
theorem decode_width (nBits label : Bits) : (decode nBits label).1.index.length ≤ label.length := by
  unfold decode
  dsimp only
  split
  · exact le_rfl
  · split
    · exact sub_length label nBits
    · exact sub_length label (twice nBits)

def decodeBound (N I : ℕ) : ℕ := 128*(N+I+2)+16

theorem decode_bound (nBits label : Bits) (N I : ℕ)
    (hn : nBits.length ≤ N) (hi : label.length ≤ I) :
    (decode nBits label).2 ≤ decodeBound N I := by
  have ha := (BinaryArithmetic.compare_spec label nBits).2.2
  have hb := (BinaryArithmetic.compare_spec label (twice nBits)).2.2
  have hs := (BinaryDivision.sub_spec label nBits).2.2
  have ht := (BinaryDivision.sub_spec label (twice nBits)).2.2
  have hma : max label.length nBits.length ≤ I+N := by omega
  have hmb : max label.length (twice nBits).length ≤ I+N+1 := by
    simp only [twice,List.length_cons]
    omega
  have htw : (twice nBits).length=nBits.length+1 := rfl
  rw [htw] at ht hb hmb
  unfold decode decodeBound
  dsimp only
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

inductive CellMode where
  | direct | sameOrEdge | absent
  deriving DecidableEq, Repr

def mode : Kind → Kind → CellMode
  | .core,.core => .direct
  | .source,.core => .direct
  | .core,.sink => .direct
  | .source,.sink => .sameOrEdge
  | _,_ => .absent

/-- Fixed port adjacency, with the source-to-sink diagonal recognized before
any input-cell read. All original graph reads retain the certified read/copy charge. -/
def adjacent (a b : PortCode) (table : Value) : Option Bool × ℕ :=
  match mode a.kind b.kind with
  | .absent => (some false,4)
  | .direct =>
      let r := EncodedCellAccess.flag a.index b.index table
      (r.1,r.2+4)
  | .sameOrEdge =>
      let c := BinaryArithmetic.compare a.index b.index
      if c.equal then (some true,c.steps+8) else
        let r := EncodedCellAccess.flag a.index b.index table
        (r.1,c.steps+r.2+12)

inductive AdjacentExec (a b : PortCode) (table : Value) : Option Bool → ℕ → Prop
  | absent : mode a.kind b.kind=.absent → AdjacentExec a b table (some false) 4
  | direct (out : Option Bool) (q : ℕ) : mode a.kind b.kind=.direct →
      FlagCellExec a.index b.index table out q → AdjacentExec a b table out (q+4)
  | same : mode a.kind b.kind=.sameOrEdge →
      (BinaryArithmetic.compare a.index b.index).equal=true →
      AdjacentExec a b table (some true) ((BinaryArithmetic.compare a.index b.index).steps+8)
  | edge (out : Option Bool) (q : ℕ) : mode a.kind b.kind=.sameOrEdge →
      (BinaryArithmetic.compare a.index b.index).equal=false →
      FlagCellExec a.index b.index table out q →
      AdjacentExec a b table out ((BinaryArithmetic.compare a.index b.index).steps+q+12)

theorem adjacent_exec (a b : PortCode) (table : Value) :
    AdjacentExec a b table (adjacent a b table).1 (adjacent a b table).2 := by
  cases hm : mode a.kind b.kind with
  | absent => simpa only [adjacent,hm] using AdjacentExec.absent (table := table) hm
  | direct => simpa only [adjacent,hm] using
      AdjacentExec.direct _ _ hm (flagCell_exec a.index b.index table)
  | sameOrEdge =>
      cases he : (BinaryArithmetic.compare a.index b.index).equal with
      | true => simpa only [adjacent,hm,he,ite_true] using AdjacentExec.same (table := table) hm he
      | false => simpa only [adjacent,hm,he,Bool.false_eq_true,ite_false] using
          AdjacentExec.edge _ _ hm he (flagCell_exec a.index b.index table)

theorem AdjacentExec.result {a b : PortCode} {table : Value} {out : Option Bool} {q : ℕ}
    (h : AdjacentExec a b table out q) : out=(adjacent a b table).1 ∧ q=(adjacent a b table).2 := by
  cases h with
  | absent hm => constructor <;> simp only [adjacent,hm]
  | direct out q hm hr =>
      have hh := hr.result
      constructor <;> simp only [adjacent,hm,← hh.1,← hh.2]
  | same hm he => constructor <;> simp only [adjacent,hm,he,ite_true]
  | edge out q hm he hr =>
      have hh := hr.result
      constructor <;> simp only [adjacent,hm,he,Bool.false_eq_true,ite_false,← hh.1,← hh.2]

private theorem equal_index {n : ℕ} (a b : Bits) (u v : Fin n)
    (hu : value a=u.val) (hv : value b=v.val) :
    (BinaryArithmetic.compare a b).equal=decide (u=v) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [hu,hv,decide_eq_true_eq,Fin.ext_iff] using
    (BinaryArithmetic.compare_spec a b).2.1

theorem adjacent_refines {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (a b : PortCode) (u v : EncodedPortPreparation.Port n)
    (ha : observe a=observePort u) (hb : observe b=observePort v) :
    (adjacent a b (EncodedCellAccess.flagTable D.adjacency)).1=
      some (EncodedPortPreparation.portAdj D u v) := by
  rcases a with ⟨ak,ai⟩
  rcases b with ⟨bk,bi⟩
  rcases u with u | u <;> rcases v with v | v
  · simp only [observe,observePort,Prod.mk.injEq] at ha hb
    rcases ha with ⟨rfl,ha⟩
    rcases hb with ⟨rfl,hb⟩
    simpa only [adjacent,mode,EncodedPortPreparation.portAdj] using
      EncodedCellAccess.flag_get D.adjacency u v ai bi ha hb
  · rcases v with v | v
    all_goals
      simp only [observe,observePort,Prod.mk.injEq] at ha hb
      rcases ha with ⟨rfl,ha⟩
      rcases hb with ⟨rfl,hb⟩
    · rfl
    · simpa only [adjacent,mode,EncodedPortPreparation.portAdj] using
        EncodedCellAccess.flag_get D.adjacency u v ai bi ha hb
  · rcases u with u | u
    all_goals
      simp only [observe,observePort,Prod.mk.injEq] at ha hb
      rcases ha with ⟨rfl,ha⟩
      rcases hb with ⟨rfl,hb⟩
    · simpa only [adjacent,mode,EncodedPortPreparation.portAdj] using
        EncodedCellAccess.flag_get D.adjacency u v ai bi ha hb
    · rfl
  · rcases u with u | u <;> rcases v with v | v
    all_goals
      simp only [observe,observePort,Prod.mk.injEq] at ha hb
      rcases ha with ⟨rfl,ha⟩
      rcases hb with ⟨rfl,hb⟩
    · rfl
    · have hc := EncodedCellAccess.flag_get D.adjacency u v ai bi ha hb
      have he := equal_index ai bi u v ha hb
      by_cases h : u=v <;> simp [adjacent,mode,EncodedPortPreparation.portAdj,he,h,hc]
    · rfl
    · rfl

def adjacentBound (n I : ℕ) : ℕ := read2Bound n n I 2+16*(I+1)+20

theorem adjacent_bound {n : ℕ} (table : Vector (Vector Bool n) n)
    (a b : PortCode) (I : ℕ) (ha : a.index.length≤I) (hb : b.index.length≤I) :
    (adjacent a b (EncodedCellAccess.flagTable table)).2 ≤ adjacentBound n I := by
  have hr := EncodedCellAccess.flag_bound table a.index b.index I ha hb
  have hc := (BinaryArithmetic.compare_spec a.index b.index).2.2
  have hm : max a.index.length b.index.length≤I := max_le ha hb
  unfold adjacent adjacentBound
  split
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only
    split <;> dsimp only <;> omega

def cell (nBits i j : Bits) (table : Value) : Option Bool × ℕ :=
  let a := decode nBits i
  let b := decode nBits j
  let r := adjacent a.1 b.1 table
  (r.1,a.2+b.2+r.2+12)

inductive CellExec (nBits i j : Bits) (table : Value) : Option Bool → ℕ → Prop
  | make (a b : PortCode) (out : Option Bool) (p q r : ℕ) :
      DecodeExec nBits i a p → DecodeExec nBits j b q → AdjacentExec a b table out r →
      CellExec nBits i j table out (p+q+r+12)

theorem cell_exec (nBits i j : Bits) (table : Value) :
    CellExec nBits i j table (cell nBits i j table).1 (cell nBits i j table).2 :=
  .make _ _ _ _ _ _ (decode_exec nBits i) (decode_exec nBits j)
    (adjacent_exec (decode nBits i).1 (decode nBits j).1 table)

theorem CellExec.result {nBits i j : Bits} {table : Value} {out : Option Bool} {q : ℕ}
    (h : CellExec nBits i j table out q) : out=(cell nBits i j table).1 ∧ q=(cell nBits i j table).2 := by
  cases h with
  | make a b out p q r ha hb hr =>
      have h1 := ha.result
      have h2 := hb.result
      have h3 := hr.result
      constructor <;> simp only [cell,← h1.1,← h1.2,← h2.1,← h2.2,← h3.1,← h3.2]

theorem cell_refines {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (nBits ib jb : Bits) (hn : value nBits=n) (i j : Fin (3*n))
    (hi : value ib=i.val) (hj : value jb=j.val) :
    (cell nBits ib jb (EncodedCellAccess.flagTable D.adjacency)).1=
      some (EncodedPortPreparation.portData D).adjacency[i.val][j.val] := by
  simpa only [cell,EncodedPortPreparation.portData,Vector.getElem_ofFn] using
    adjacent_refines D _ _ _ _ (decode_refines nBits ib hn i hi)
      (decode_refines nBits jb hn j hj)

theorem cell_bound {n : ℕ} (table : Vector (Vector Bool n) n)
    (nBits i j : Bits) (N I : ℕ) (hn : nBits.length≤N)
    (hi : i.length≤I) (hj : j.length≤I) :
    (cell nBits i j (EncodedCellAccess.flagTable table)).2 ≤
      2*decodeBound N I+adjacentBound n I+12 := by
  have ha := decode_bound nBits i N I hn hi
  have hb := decode_bound nBits j N I hn hj
  have hr := adjacent_bound table (decode nBits i).1 (decode nBits j).1 I
    ((decode_width nBits i).trans hi) ((decode_width nBits j).trans hj)
  change (decode nBits i).2+(decode nBits j).2+
    (adjacent (decode nBits i).1 (decode nBits j).1 (EncodedCellAccess.flagTable table)).2+12 ≤ _
  omega

theorem CellExec.cost {n : ℕ} (table : Vector (Vector Bool n) n)
    {nBits i j : Bits} {out : Option Bool} {q : ℕ}
    (run : CellExec nBits i j (EncodedCellAccess.flagTable table) out q)
    (N I : ℕ) (hn : nBits.length≤N) (hi : i.length≤I) (hj : j.length≤I) :
    q ≤ 2*decodeBound N I+adjacentBound n I+12 := by
  rw [run.result.2]
  exact cell_bound table nBits i j N I hn hi hj

/-- Only weighted cores inspect the retained low mask. Both terminal kinds
return false without reading it, including when an unused mask is malformed. -/
def removed (p : PortCode) (low : Value) : Option Bool × ℕ :=
  match p.kind with
  | .core => let r := flagAt p.index low; (r.1,r.2+4)
  | .source | .sink => (some false,4)

inductive RemovedExec (p : PortCode) (low : Value) : Option Bool → ℕ → Prop
  | core (out : Option Bool) (q : ℕ) : p.kind=.core → FlagAtExec p.index low out q →
      RemovedExec p low out (q+4)
  | source : p.kind=.source → RemovedExec p low (some false) 4
  | sink : p.kind=.sink → RemovedExec p low (some false) 4

theorem removed_exec (p : PortCode) (low : Value) :
    RemovedExec p low (removed p low).1 (removed p low).2 := by
  cases hk : p.kind with
  | core => simpa only [removed,hk] using RemovedExec.core _ _ hk (flagAt_exec p.index low)
  | source => simpa only [removed,hk] using RemovedExec.source (low := low) hk
  | sink => simpa only [removed,hk] using RemovedExec.sink (low := low) hk

theorem RemovedExec.result {p : PortCode} {low : Value} {out : Option Bool} {q : ℕ}
    (h : RemovedExec p low out q) : out=(removed p low).1 ∧ q=(removed p low).2 := by
  cases h with
  | core out q hk hr =>
      have hh := hr.result
      constructor <;> simp only [removed,hk,← hh.1,← hh.2]
  | source hk => constructor <;> simp only [removed,hk]
  | sink hk => constructor <;> simp only [removed,hk]

theorem removed_refines {n : ℕ} (low : Vector Bool n) (p : PortCode)
    (v : EncodedPortPreparation.Port n) (hp : observe p=observePort v) :
    (removed p (maskValue low)).1=some (match v with | .inl u => low[u.val]'u.isLt | .inr _ => false) := by
  rcases p with ⟨kind,index⟩
  rcases v with v | v
  · have hk : kind=.core := congrArg Prod.fst hp
    have hi : value index=v.val := congrArg Prod.snd hp
    subst kind
    simpa only [removed] using flagAt_get low v index hi
  · cases v with
    | inl v =>
        have hk : kind=.source := congrArg Prod.fst hp
        subst kind
        rfl
    | inr v =>
        have hk : kind=.sink := congrArg Prod.fst hp
        subst kind
        rfl

def removalCell (nBits label : Bits) (low : Value) : Option Bool × ℕ :=
  let p := decode nBits label
  let r := removed p.1 low
  (r.1,p.2+r.2+8)

inductive RemovalCellExec (nBits label : Bits) (low : Value) : Option Bool → ℕ → Prop
  | make (p : PortCode) (out : Option Bool) (q r : ℕ) :
      DecodeExec nBits label p q → RemovedExec p low out r →
      RemovalCellExec nBits label low out (q+r+8)

theorem removalCell_exec (nBits label : Bits) (low : Value) :
    RemovalCellExec nBits label low (removalCell nBits label low).1 (removalCell nBits label low).2 :=
  .make _ _ _ _ (decode_exec nBits label) (removed_exec (decode nBits label).1 low)

theorem RemovalCellExec.result {nBits label : Bits} {low : Value} {out : Option Bool} {q : ℕ}
    (h : RemovalCellExec nBits label low out q) :
    out=(removalCell nBits label low).1 ∧ q=(removalCell nBits label low).2 := by
  cases h with
  | make p out q r hp hr =>
      have hh := hp.result
      have ht := hr.result
      constructor <;> simp only [removalCell,← hh.1,← hh.2,← ht.1,← ht.2]

theorem removalCell_refines {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (nBits label : Bits) (hn : value nBits=n) (i : Fin (3*n)) (hi : value label=i.val) :
    (removalCell nBits label (maskValue (EncodedPortPreparation.lowMask D))).1=
      some (EncodedPortPreparation.portData D).removed[i.val] := by
  have hd := decode_refines nBits label hn i hi
  simp only [removalCell,EncodedPortPreparation.portData,Vector.getElem_ofFn,Fin.eta]
  cases he : EncodedPortPreparation.decodePort i with
  | inl v =>
      have hk : (decode nBits label).1.kind=.core := by
        simpa only [observe,he,observePort] using congrArg Prod.fst hd
      have hv : value (decode nBits label).1.index=v.val := by
        simpa only [observe,he,observePort] using congrArg Prod.snd hd
      simp only [removed,hk]
      exact flagAt_get (EncodedPortPreparation.lowMask D) v (decode nBits label).1.index hv
  | inr v =>
      cases v with
      | inl v =>
          have hk : (decode nBits label).1.kind=.source := by
            simpa only [observe,he,observePort] using congrArg Prod.fst hd
          simp only [removed,hk]
      | inr v =>
          have hk : (decode nBits label).1.kind=.sink := by
            simpa only [observe,he,observePort] using congrArg Prod.fst hd
          simp only [removed,hk]

/-- The exact computed binary low flags enter the port-data callback. The raw
input interpretation preserves original weight fields and current query-cost fields. -/
theorem prepared_removal_refines {n : ℕ} (adjacency : Vector (Vector Bool n) n)
    (w c : BinaryFractionalRows.Row n) (nBits label : Bits) (hn : value nBits=n)
    (i : Fin (3*n)) (hi : value label=i.val) :
    (removalCell nBits label (maskValue (BinaryPortWeightPreparation.prepare nBits w c).low)).1=
      some (EncodedPortPreparation.portData (BinaryUnitCostParameters.rawInput adjacency w c)).removed[i.val] := by
  rw [BinaryPortWeightPreparation.prepare_low nBits hn adjacency w c]
  exact removalCell_refines _ nBits label hn i hi

theorem removalCell_bound {n : ℕ} (low : Vector Bool n) (nBits label : Bits)
    (N I : ℕ) (hn : nBits.length≤N) (hi : label.length≤I) :
    (removalCell nBits label (maskValue low)).2 ≤ decodeBound N I+20*(n+1)*(I+1)+24 := by
  have hd := decode_bound nBits label N I hn hi
  have hr := flagAt_bound low (decode nBits label).1.index I ((decode_width nBits label).trans hi)
  unfold removalCell removed
  dsimp only
  split <;> dsimp only <;> omega

theorem RemovalCellExec.cost {n : ℕ} (low : Vector Bool n)
    {nBits label : Bits} {out : Option Bool} {q : ℕ}
    (run : RemovalCellExec nBits label (maskValue low) out q)
    (N I : ℕ) (hn : nBits.length≤N) (hi : label.length≤I) :
    q ≤ decodeBound N I+20*(n+1)*(I+1)+24 := by
  rw [run.result.2]
  exact removalCell_bound low nBits label N I hn hi

/-- Finite observation of the actual retained decoder result; constructing
this observation is not a hidden runtime call or a source of a free copy. -/
def portValue (p : PortCode) : Value :=
  .pair (.word (match p.kind with | .core => [] | .source => [true] | .sink => [false,true]))
    (.word p.index)

theorem portValue_size (p : PortCode) : (portValue p).size ≤ p.index.length+5 := by
  rcases p with ⟨kind,index⟩
  cases kind <;> simp only [portValue,Value.size,List.length_nil,List.length_cons] <;> omega

theorem decode_size (nBits label : Bits) :
    (portValue (decode nBits label).1).size ≤ label.length+5 := by
  exact (portValue_size _).trans (Nat.add_le_add_right (decode_width nBits label) 5)

end DirectedFlowCutGap.BinaryPortDecode
