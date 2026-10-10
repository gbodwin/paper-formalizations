import DirectedFlowCutGap.BinaryPortDecode

/-!
# Fixed binary generation and materialization of the permanent port graph

The original retained dimension word drives a literal binary triple, followed
by a zero/predecessor-controlled ascending-label loop. Each retained label is
copied by the named bit-list body. The two fixed finite traversals then call
only the certified permanent-port adjacency and removal bodies. No native
`finRange`, arbitrary map callback, or natural-number loop runs in this code.

The port count is 3*n; the original n and its padded input word remain separate.
Raw weight and penalized query-cost fields are read only through the earlier
preparation interface. Both optional outputs and all reached local charges
are retained, including on malformed input. Refinement maps below describe
actual produced values and are not additional executable conversions.

This closes label/table/mask construction from already retained adjacency and
low-mask values. Their input construction, survivor-ordered restriction and
weight/cost gathering, replica/chain materialization, and the common immutable
reference/list simulation overhead remain explicit separate joins. Local
closed execution derivations do not by themselves assert native Lean time.
-/
namespace DirectedFlowCutGap.BinaryPortMaterialization
open BinaryArithmetic EncodedSequenceAccess EncodedRestrictedTestExec

/-- One zero-bit constructor, the named binary adder, and a result record. -/
def triple (nBits : Bits) : Bits × ℕ :=
  let r := addCanonical nBits (BinaryPortDecode.twice nBits)
  (r.1,r.2+8)

theorem triple_value (nBits : Bits) : value (triple nBits).1=3*value nBits := by
  simp only [triple,(canonical_values _ _).1,BinaryPortDecode.twice_value]
  omega

theorem triple_width (nBits : Bits) (D : ℕ) (hD : nBits.length ≤ D) :
    (triple nBits).1.length ≤ D+2 := by
  have h := value_lt nBits
  have hp : 2^nBits.length ≤ 2^D := Nat.pow_le_pow_right (by omega) hD
  have h3 : 3*value nBits<2^(D+2) := by
    simp only [pow_add] at *
    norm_num at *
    omega
  change (addCanonical nBits (BinaryPortDecode.twice nBits)).1.length ≤ D+2
  rw [(canonical_values _ _).2.2.1,BinaryPortDecode.twice_value]
  apply Nat.size_le.mpr
  omega

theorem triple_bound (nBits : Bits) (D : ℕ) (hD : nBits.length ≤ D) :
    (triple nBits).2 ≤ 32*(D+3)+8 := by
  have hn : nBits.length ≤ D+1 := by omega
  have ht : (BinaryPortDecode.twice nBits).length ≤ D+1 := by
    simpa only [BinaryPortDecode.twice,List.length_cons] using Nat.add_le_add_right hD 1
  have h := (canonical_charges hn ht).1
  exact Nat.add_le_add_right h 8

/-- Only binary words are executable loop controls. -/
def labels (fuel counter : Bits) : List Bits × ℕ :=
  let z := isZero fuel
  if hz : z.1=true then ([],z.2+4) else
    let p := predecessor fuel
    let s := addCanonical counter [true]
    let c := copyBits counter
    let r := labels p.1 s.1
    (c.1::r.1,z.2+p.2+s.2+c.2+r.2+16)
termination_by value fuel
decreasing_by
  have hv : 0<value fuel := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec fuel).1.mpr h))
  rw [(predecessor_spec fuel).1]
  omega

/-- Every constructor names its fixed scalar calls; there is no host callback rule. -/
inductive LabelsExec : Bits → Bits → List Bits → ℕ → Prop
  | zero (fuel counter : Bits) : (isZero fuel).1=true →
      LabelsExec fuel counter [] ((isZero fuel).2+4)
  | step (fuel counter copied : Bits) (tail : List Bits) (copyCharge tailCharge : ℕ) :
      (isZero fuel).1=false → BitsCopyExec counter copied copyCharge →
      LabelsExec (predecessor fuel).1 (addCanonical counter [true]).1 tail tailCharge →
      LabelsExec fuel counter (copied::tail)
        ((isZero fuel).2+(predecessor fuel).2+(addCanonical counter [true]).2+
          copyCharge+tailCharge+16)

theorem LabelsExec.result {fuel counter : Bits} {out : List Bits} {q : ℕ}
    (h : LabelsExec fuel counter out q) :
    out=(labels fuel counter).1 ∧ q=(labels fuel counter).2 := by
  induction h with
  | zero fuel counter hz => constructor <;> rw [labels] <;> simp only [hz,dite_eq_left]
  | step fuel counter copied tail copyCharge tailCharge hz hc hr ih =>
      have hh := hc.result
      constructor <;> rw [labels] <;>
        simp only [hz,Bool.false_eq_true,dite_false,← hh.1,← hh.2,← ih.1,← ih.2]

private theorem labels_exec_aux (k : ℕ) (fuel counter : Bits) (hk : value fuel=k) :
    LabelsExec fuel counter (labels fuel counter).1 (labels fuel counter).2 := by
  induction k generalizing fuel counter with
  | zero =>
      have hz := (isZero_spec fuel).1.mpr hk
      rw [labels]
      simpa only [hz,dite_eq_left] using LabelsExec.zero fuel counter hz
  | succ k ih =>
      have hz : (isZero fuel).1=false := Bool.eq_false_iff.mpr (by
        intro h; have hv := (isZero_spec fuel).1.mp h; omega)
      have hp : value (predecessor fuel).1=k := by rw [(predecessor_spec fuel).1,hk]; omega
      have hr := ih (predecessor fuel).1 (addCanonical counter [true]).1 hp
      rw [labels]
      simpa only [hz,Bool.false_eq_true,dite_false] using
        LabelsExec.step fuel counter _ _ _ _ hz (copyBits_exec counter) hr

theorem labels_exec (fuel counter : Bits) :
    LabelsExec fuel counter (labels fuel counter).1 (labels fuel counter).2 :=
  labels_exec_aux (value fuel) fuel counter rfl

private theorem successor_normal (counter : Bits) : Normal (addCanonical counter [true]).1 :=
  (trim_spec (add false counter [true]).1).1

private theorem successor_value (counter : Bits) :
    value (addCanonical counter [true]).1=value counter+1 := by
  simpa only [value,Bool.toNat_true,mul_zero,add_zero] using (canonical_values counter [true]).1

/-- Exact order and exact stored bytes, not merely an unordered set of indices. -/
theorem labels_refines (k : ℕ) (fuel counter : Bits) (hk : value fuel=k) (hc : Normal counter) :
    (labels fuel counter).1=(List.range' (value counter) k).map Nat.bits := by
  induction k generalizing fuel counter with
  | zero =>
      have hz := (isZero_spec fuel).1.mpr hk
      rw [labels]
      simp only [hz,dite_eq_left,List.range'_zero,List.map_nil]
  | succ k ih =>
      have hz : (isZero fuel).1=false := Bool.eq_false_iff.mpr (by
        intro h; have hv := (isZero_spec fuel).1.mp h; omega)
      have hp : value (predecessor fuel).1=k := by rw [(predecessor_spec fuel).1,hk]; omega
      have hr := ih (predecessor fuel).1 (addCanonical counter [true]).1 hp (successor_normal counter)
      rw [labels]
      simp only [hz,Bool.false_eq_true,dite_false,(copyBits_spec counter).1,hr,
        successor_value,List.range'_succ,List.map_cons,normal_bits hc]

/-- This is an invariant of the actual remaining fuel and next retained index. -/
def CounterBound (fuel counter : Bits) (B : ℕ) : Prop :=
  fuel.length ≤ B ∧ counter.length ≤ B ∧ value fuel+value counter<2^B

theorem counter_step {fuel counter : Bits} {B : ℕ} (h : CounterBound fuel counter B)
    (hz : (isZero fuel).1=false) :
    CounterBound (predecessor fuel).1 (addCanonical counter [true]).1 B := by
  have hp : 0<value fuel := by
    by_contra hn
    have hv : value fuel=0 := by omega
    have he := (isZero_spec fuel).1.mpr hv
    simp [hz] at he
  refine ⟨?_,?_,?_⟩
  · rw [(predecessor_spec fuel).2.1]
    apply Nat.size_le.mpr
    have hh := h.2.2
    omega
  · rw [(canonical_values counter [true]).2.2.1]
    apply Nat.size_le.mpr
    have hh := h.2.2
    simp only [value,Bool.toNat_true,mul_zero,add_zero]
    omega
  · rw [(predecessor_spec fuel).1,successor_value]
    have hh := h.2.2
    omega

def labelsBound (length B : ℕ) : ℕ := (length+1)*128*(B+3)

/-- The induction bounds every reached counter and every returned suffix. -/
theorem labels_bounds (k : ℕ) (fuel counter : Bits) (hk : value fuel=k)
    (B : ℕ) (h : CounterBound fuel counter B) :
    (labels fuel counter).1.length=k ∧
    (∀ word∈(labels fuel counter).1, word.length ≤ B) ∧
    (labels fuel counter).2 ≤ labelsBound k B := by
  induction k generalizing fuel counter with
  | zero =>
      have hz := (isZero_spec fuel).1.mpr hk
      have hb := (isZero_spec fuel).2
      have hw := h.1
      rw [labels]
      simp only [hz,dite_eq_left,List.length_nil,List.not_mem_nil,false_implies,implies_true,true_and]
      unfold labelsBound
      omega
  | succ k ih =>
      have hz : (isZero fuel).1=false := Bool.eq_false_iff.mpr (by
        intro he; have hv := (isZero_spec fuel).1.mp he; omega)
      have hp : value (predecessor fuel).1=k := by rw [(predecessor_spec fuel).1,hk]; omega
      have hs := counter_step h hz
      have hr := ih (predecessor fuel).1 (addCanonical counter [true]).1 hp hs
      have hzq := (isZero_spec fuel).2
      have hpq := (predecessor_spec fuel).2.2
      have hcq := (copyBits_spec counter).2
      have hcw : counter.length ≤ B+1 := by have hh:=h.2.1; omega
      have hsq := (canonical_charges hcw (show ([true] : Bits).length ≤ B+1 by simp)).1
      have hfw := h.1
      have hbw := h.2.1
      rw [labels]
      simp only [hz,Bool.false_eq_true,dite_false,(copyBits_spec counter).1,List.length_cons]
      refine ⟨by omega,?_,?_⟩
      · intro word hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h.2.1
        · exact hr.2.1 word hw
      · have hh := hr.2.2
        unfold labelsBound at *
        nlinarith

def labelValue (words : List Bits) : Value := EncodedSequenceAccess.sequence (words.map Value.word)

theorem labelValue_size {words : List Bits} {B : ℕ}
    (h : ∀ word∈words, word.length ≤ B) :
    (labelValue words).size ≤ words.length*(B+2)+1 := by
  have hh := sequence_size_bound (xs := words.map Value.word) (S := B+1) (by
    intro x hx
    obtain ⟨word,hw,rfl⟩ := List.mem_map.mp hx
    exact Nat.add_le_add_right (h word hw) 1)
  simpa only [labelValue,List.length_map,Nat.add_assoc] using hh

/-- Prefixes and suffixes held across recursive calls fit the same complete-list envelope. -/
theorem labelValue_parts {words : List Bits} {B : ℕ}
    (h : ∀ word∈words, word.length ≤ B) (k : ℕ) :
    (labelValue (words.take k)).size ≤ words.length*(B+2)+1 ∧
    (labelValue (words.drop k)).size ≤ words.length*(B+2)+1 := by
  constructor
  · exact (labelValue_size (fun w hw => h w (List.mem_of_mem_take hw))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right (B+2) (List.length_take_le' k words)) 1)
  · exact (labelValue_size (fun w hw => h w (List.mem_of_mem_drop hw))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right (B+2) (by simp only [List.length_drop]; omega)) 1)

private theorem range_bits (m : ℕ) :
    (List.range' 0 m).map Nat.bits=(List.finRange m).map (fun i => i.val.bits) := by
  rw [← List.range_eq_range']
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

def portLabels (nBits : Bits) : List Bits × ℕ :=
  let t := triple nBits
  let r := labels t.1 []
  (r.1,t.2+r.2+4)

theorem portLabels_refines {n : ℕ} (nBits : Bits) (hn : value nBits=n) :
    (portLabels nBits).1=(List.finRange (3*n)).map (fun i => i.val.bits) := by
  have ht : value (triple nBits).1=3*n := by rw [triple_value,hn]
  exact (labels_refines (3*n) (triple nBits).1 [] ht .nil).trans (range_bits (3*n))

theorem portLabels_bounds {n : ℕ} (nBits : Bits) (hn : value nBits=n) (D : ℕ)
    (hD : nBits.length ≤ D) :
    (portLabels nBits).1.length=3*n ∧
    (∀ word∈(portLabels nBits).1, word.length ≤ D+2) ∧
    (portLabels nBits).2 ≤ 32*(D+3)+8+labelsBound (3*n) (D+2)+4 := by
  have ht : value (triple nBits).1=3*n := by rw [triple_value,hn]
  have hw := triple_width nBits D hD
  have hc : CounterBound (triple nBits).1 [] (D+2) := by
    refine ⟨hw,by simp,?_⟩
    have h := value_lt (triple nBits).1
    have hp : 2^(triple nBits).1.length ≤ 2^(D+2) := Nat.pow_le_pow_right (by omega) hw
    simpa only [value,add_zero] using h.trans_le hp
  have h := labels_bounds (3*n) (triple nBits).1 [] ht (D+2) hc
  have hq := triple_bound nBits D hD
  exact ⟨h.1,h.2.1,by dsimp only [portLabels]; omega⟩

theorem portLabels_valid {n : ℕ} (nBits : Bits) (hn : value nBits=n)
    (word : Bits) (hw : word∈(portLabels nBits).1) : value word<3*n := by
  rw [portLabels_refines nBits hn] at hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  simpa only [value_bits] using i.isLt

/-- Decoder records and the doubled dimension also fit the reached word envelope. -/
theorem portLabels_decode_shapes {n : ℕ} (nBits : Bits) (hn : value nBits=n)
    (D : ℕ) (hD : nBits.length ≤ D) (word : Bits) (hw : word∈(portLabels nBits).1) :
    (BinaryPortDecode.twice nBits).length ≤ D+1 ∧
    (BinaryPortDecode.decode nBits word).1.index.length ≤ D+2 ∧
    (BinaryPortDecode.portValue (BinaryPortDecode.decode nBits word).1).size ≤ D+7 := by
  have hword := (portLabels_bounds nBits hn D hD).2.1 word hw
  refine ⟨?_,(BinaryPortDecode.decode_width nBits word).trans hword,?_⟩
  · simpa only [BinaryPortDecode.twice,List.length_cons] using Nat.add_le_add_right hD 1
  · have hs := BinaryPortDecode.decode_size nBits word
    omega

/-- These modes select two specific certified bodies, never a supplied function. -/
inductive Mode where
  | adjacency (source : Bits)
  | removal
  deriving DecidableEq, Repr

def test (nBits : Bits) (adjacency low : Value) (mode : Mode) (target : Bits) :
    Option Bool × ℕ :=
  match mode with
  | .adjacency source => let r := BinaryPortDecode.cell nBits source target adjacency; (r.1,r.2+4)
  | .removal => let r := BinaryPortDecode.removalCell nBits target low; (r.1,r.2+4)

inductive TestExec (nBits : Bits) (adjacency low : Value) : Mode → Bits → Option Bool → ℕ → Prop
  | adjacency (source target : Bits) (out : Option Bool) (q : ℕ) :
      BinaryPortDecode.CellExec nBits source target adjacency out q →
      TestExec nBits adjacency low (.adjacency source) target out (q+4)
  | removal (target : Bits) (out : Option Bool) (q : ℕ) :
      BinaryPortDecode.RemovalCellExec nBits target low out q →
      TestExec nBits adjacency low .removal target out (q+4)

theorem test_exec (nBits : Bits) (adjacency low : Value) (mode : Mode) (target : Bits) :
    TestExec nBits adjacency low mode target
      (test nBits adjacency low mode target).1 (test nBits adjacency low mode target).2 := by
  cases mode with
  | adjacency source => exact .adjacency _ _ _ _ (BinaryPortDecode.cell_exec nBits source target adjacency)
  | removal => exact .removal _ _ _ (BinaryPortDecode.removalCell_exec nBits target low)

theorem TestExec.result {nBits : Bits} {adjacency low : Value} {mode : Mode} {target : Bits}
    {out : Option Bool} {q : ℕ} (h : TestExec nBits adjacency low mode target out q) :
    out=(test nBits adjacency low mode target).1 ∧ q=(test nBits adjacency low mode target).2 := by
  cases h with
  | adjacency source target out q h =>
      have hh := h.result
      constructor <;> simp only [test,← hh.1,← hh.2]
  | removal target out q h =>
      have hh := h.result
      constructor <;> simp only [test,← hh.1,← hh.2]

def row (nBits : Bits) (adjacency low : Value) (mode : Mode) : List Bits → Option Value × ℕ
  | [] => (some .empty,1)
  | target::targets =>
      let a := test nBits adjacency low mode target
      match a.1 with
      | none => (none,a.2+4)
      | some b =>
          let r := row nBits adjacency low mode targets
          match r.1 with
          | none => (none,a.2+r.2+8)
          | some tail => (some (.pair (.flag b) tail),a.2+r.2+12)

inductive RowExec (nBits : Bits) (adjacency low : Value) (mode : Mode) :
    List Bits → Option Value → ℕ → Prop
  | nil : RowExec nBits adjacency low mode [] (some .empty) 1
  | missingCell (target : Bits) (targets : List Bits) (q : ℕ) :
      TestExec nBits adjacency low mode target none q →
      RowExec nBits adjacency low mode (target::targets) none (q+4)
  | missingTail (target : Bits) (targets : List Bits) (b : Bool) (q r : ℕ) :
      TestExec nBits adjacency low mode target (some b) q →
      RowExec nBits adjacency low mode targets none r →
      RowExec nBits adjacency low mode (target::targets) none (q+r+8)
  | cell (target : Bits) (targets : List Bits) (b : Bool) (tail : Value) (q r : ℕ) :
      TestExec nBits adjacency low mode target (some b) q →
      RowExec nBits adjacency low mode targets (some tail) r →
      RowExec nBits adjacency low mode (target::targets) (some (.pair (.flag b) tail)) (q+r+12)

theorem RowExec.result {nBits : Bits} {adjacency low : Value} {mode : Mode}
    {targets : List Bits} {out : Option Value} {q : ℕ}
    (h : RowExec nBits adjacency low mode targets out q) :
    out=(row nBits adjacency low mode targets).1 ∧ q=(row nBits adjacency low mode targets).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | missingCell target targets q ha =>
      have a := ha.result
      constructor <;> simp only [row,← a.1,← a.2]
  | missingTail target targets b q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [row,← a.1,← a.2,← ih.1,← ih.2]
  | cell target targets b tail q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [row,← a.1,← a.2,← ih.1,← ih.2]

theorem row_exec (nBits : Bits) (adjacency low : Value) (mode : Mode) (targets : List Bits) :
    RowExec nBits adjacency low mode targets
      (row nBits adjacency low mode targets).1 (row nBits adjacency low mode targets).2 := by
  induction targets with
  | nil => exact .nil
  | cons target targets ih =>
      have ha := test_exec nBits adjacency low mode target
      cases hc : (test nBits adjacency low mode target).1 with
      | none =>
          rw [hc] at ha
          simpa only [row,hc] using RowExec.missingCell target targets _ ha
      | some b =>
          rw [hc] at ha
          cases ht : (row nBits adjacency low mode targets).1 with
          | none =>
              rw [ht] at ih
              simpa only [row,hc,ht] using RowExec.missingTail target targets b _ _ ha ih
          | some tail =>
              rw [ht] at ih
              simpa only [row,hc,ht] using RowExec.cell target targets b tail _ _ ha ih

def matrix (nBits : Bits) (adjacency low : Value) (targets : List Bits) :
    List Bits → Option Value × ℕ
  | [] => (some .empty,1)
  | source::sources =>
      let a := row nBits adjacency low (.adjacency source) targets
      match a.1 with
      | none => (none,a.2+4)
      | some cells =>
          let r := matrix nBits adjacency low targets sources
          match r.1 with
          | none => (none,a.2+r.2+8)
          | some tail => (some (.pair cells tail),a.2+r.2+12)

inductive MatrixExec (nBits : Bits) (adjacency low : Value) (targets : List Bits) :
    List Bits → Option Value → ℕ → Prop
  | nil : MatrixExec nBits adjacency low targets [] (some .empty) 1
  | missingRow (source : Bits) (sources : List Bits) (q : ℕ) :
      RowExec nBits adjacency low (.adjacency source) targets none q →
      MatrixExec nBits adjacency low targets (source::sources) none (q+4)
  | missingTail (source : Bits) (sources : List Bits) (cells : Value) (q r : ℕ) :
      RowExec nBits adjacency low (.adjacency source) targets (some cells) q →
      MatrixExec nBits adjacency low targets sources none r →
      MatrixExec nBits adjacency low targets (source::sources) none (q+r+8)
  | row (source : Bits) (sources : List Bits) (cells tail : Value) (q r : ℕ) :
      RowExec nBits adjacency low (.adjacency source) targets (some cells) q →
      MatrixExec nBits adjacency low targets sources (some tail) r →
      MatrixExec nBits adjacency low targets (source::sources) (some (.pair cells tail)) (q+r+12)

theorem MatrixExec.result {nBits : Bits} {adjacency low : Value} {targets sources : List Bits}
    {out : Option Value} {q : ℕ} (h : MatrixExec nBits adjacency low targets sources out q) :
    out=(matrix nBits adjacency low targets sources).1 ∧
      q=(matrix nBits adjacency low targets sources).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | missingRow source sources q ha =>
      have a := ha.result
      constructor <;> simp only [matrix,← a.1,← a.2]
  | missingTail source sources cells q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [matrix,← a.1,← a.2,← ih.1,← ih.2]
  | row source sources cells tail q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [matrix,← a.1,← a.2,← ih.1,← ih.2]

theorem matrix_exec (nBits : Bits) (adjacency low : Value) (targets sources : List Bits) :
    MatrixExec nBits adjacency low targets sources
      (matrix nBits adjacency low targets sources).1 (matrix nBits adjacency low targets sources).2 := by
  induction sources with
  | nil => exact .nil
  | cons source sources ih =>
      have ha := row_exec nBits adjacency low (.adjacency source) targets
      cases hc : (row nBits adjacency low (.adjacency source) targets).1 with
      | none =>
          rw [hc] at ha
          simpa only [matrix,hc] using MatrixExec.missingRow source sources _ ha
      | some cells =>
          rw [hc] at ha
          cases ht : (matrix nBits adjacency low targets sources).1 with
          | none =>
              rw [ht] at ih
              simpa only [matrix,hc,ht] using MatrixExec.missingTail source sources cells _ _ ha ih
          | some tail =>
              rw [ht] at ih
              simpa only [matrix,hc,ht] using MatrixExec.row source sources cells tail _ _ ha ih

/-- This predicate describes a retained mode's only additional word. -/
def ModeBound (mode : Mode) (I : ℕ) : Prop :=
  match mode with | .adjacency source => source.length ≤ I | .removal => True

/-- One common polynomial dominates both fixed tests. -/
def testBound (n D I : ℕ) : ℕ :=
  2*BinaryPortDecode.decodeBound D I+BinaryPortDecode.adjacentBound n I+
    20*(n+1)*(I+1)+40

theorem test_bound {n : ℕ} (A : Vector (Vector Bool n) n) (low : Vector Bool n)
    (nBits target : Bits) (mode : Mode) (D I : ℕ) (hn : nBits.length ≤ D)
    (ht : target.length ≤ I) (hm : ModeBound mode I) :
    (test nBits (EncodedCellAccess.flagTable A) (maskValue low) mode target).2 ≤ testBound n D I := by
  cases mode with
  | adjacency source =>
      have h := BinaryPortDecode.cell_bound A nBits source target D I hn hm ht
      dsimp only [test]
      unfold testBound
      omega
  | removal =>
      have h := BinaryPortDecode.removalCell_bound low nBits target D I hn ht
      dsimp only [test]
      unfold testBound
      omega

def rowBound (n D I length : ℕ) : ℕ := length*(testBound n D I+12)+1

def matrixBound (n D I rows columns : ℕ) : ℕ := rows*(rowBound n D I columns+12)+1

/-- The bound includes malformed branches; no success premise hides work. -/
theorem row_bound {n : ℕ} (A : Vector (Vector Bool n) n) (low : Vector Bool n)
    (nBits : Bits) (mode : Mode) (targets : List Bits) (D I : ℕ)
    (hn : nBits.length ≤ D) (hm : ModeBound mode I)
    (ht : ∀ word∈targets, word.length ≤ I) :
    (row nBits (EncodedCellAccess.flagTable A) (maskValue low) mode targets).2 ≤ 
      rowBound n D I targets.length := by
  induction targets with
  | nil => simp [row,rowBound]
  | cons target targets ih =>
      have ha := test_bound A low nBits target mode D I hn (ht target (by simp)) hm
      have hr := ih (fun w hw => ht w (by simp [hw]))
      simp only [row,List.length_cons]
      cases hc : (test nBits (EncodedCellAccess.flagTable A) (maskValue low) mode target).1 with
      | none => simp only; unfold rowBound at *; nlinarith
      | some b =>
          cases hh : (row nBits (EncodedCellAccess.flagTable A) (maskValue low) mode targets).1 <;>
            simp only <;> unfold rowBound at * <;> nlinarith

theorem matrix_bound {n : ℕ} (A : Vector (Vector Bool n) n) (low : Vector Bool n)
    (nBits : Bits) (targets sources : List Bits) (D I : ℕ)
    (hn : nBits.length ≤ D) (ht : ∀ word∈targets, word.length ≤ I)
    (hs : ∀ word∈sources, word.length ≤ I) :
    (matrix nBits (EncodedCellAccess.flagTable A) (maskValue low) targets sources).2 ≤ 
      matrixBound n D I sources.length targets.length := by
  induction sources with
  | nil => simp [matrix,matrixBound]
  | cons source sources ih =>
      have ha := row_bound A low nBits (.adjacency source) targets D I hn (hs source (by simp)) ht
      have hr := ih (fun w hw => hs w (by simp [hw]))
      simp only [matrix,List.length_cons]
      cases hc : (row nBits (EncodedCellAccess.flagTable A) (maskValue low) (.adjacency source) targets).1 with
      | none => simp only; unfold matrixBound at *; nlinarith
      | some cells =>
          cases hh : (matrix nBits (EncodedCellAccess.flagTable A) (maskValue low) targets sources).1 <;>
            simp only <;> unfold matrixBound at * <;> nlinarith

theorem RowExec.cost {n : ℕ} (A : Vector (Vector Bool n) n) (low : Vector Bool n)
    {nBits : Bits} {mode : Mode} {targets : List Bits} {out : Option Value} {q : ℕ}
    (run : RowExec nBits (EncodedCellAccess.flagTable A) (maskValue low) mode targets out q)
    (D I : ℕ) (hn : nBits.length ≤ D) (hm : ModeBound mode I)
    (ht : ∀ word∈targets, word.length ≤ I) : q ≤ rowBound n D I targets.length := by
  rw [run.result.2]
  exact row_bound A low nBits mode targets D I hn hm ht

theorem MatrixExec.cost {n : ℕ} (A : Vector (Vector Bool n) n) (low : Vector Bool n)
    {nBits : Bits} {targets sources : List Bits} {out : Option Value} {q : ℕ}
    (run : MatrixExec nBits (EncodedCellAccess.flagTable A) (maskValue low) targets sources out q)
    (D I : ℕ) (hn : nBits.length ≤ D) (ht : ∀ word∈targets, word.length ≤ I)
    (hs : ∀ word∈sources, word.length ≤ I) :
    q ≤ matrixBound n D I sources.length targets.length := by
  rw [run.result.2]
  exact matrix_bound A low nBits targets sources D I hn ht hs

/-- Every produced row, including each recursive suffix, consists of flags. -/
theorem row_size (nBits : Bits) (adjacency low : Value) (mode : Mode) (targets : List Bits)
    (out : Value) (hout : (row nBits adjacency low mode targets).1=some out) :
    out.size ≤ 3*targets.length+1 := by
  induction targets generalizing out with
  | nil => simp only [row,Option.some.injEq] at hout; subst out; simp [Value.size]
  | cons target targets ih =>
      cases hc : (test nBits adjacency low mode target).1 with
      | none => simp [row,hc] at hout
      | some b =>
          cases ht : (row nBits adjacency low mode targets).1 with
          | none => simp [row,hc,ht] at hout
          | some tail =>
              have hb := ih tail ht
              simp only [row,hc,ht,Option.some.injEq] at hout
              subst out
              simp only [Value.size,List.length_cons]
              omega

theorem matrix_size (nBits : Bits) (adjacency low : Value) (targets sources : List Bits)
    (out : Value) (hout : (matrix nBits adjacency low targets sources).1=some out) :
    out.size ≤ sources.length*(3*targets.length+2)+1 := by
  induction sources generalizing out with
  | nil => simp only [matrix,Option.some.injEq] at hout; subst out; simp [Value.size]
  | cons source sources ih =>
      cases hc : (row nBits adjacency low (.adjacency source) targets).1 with
      | none => simp [matrix,hc] at hout
      | some cells =>
          cases ht : (matrix nBits adjacency low targets sources).1 with
          | none => simp [matrix,hc,ht] at hout
          | some tail =>
              have hb := ih tail ht
              have ha := row_size nBits adjacency low (.adjacency source) targets cells hc
              simp only [matrix,hc,ht,Option.some.injEq] at hout
              subst out
              simp only [Value.size,List.length_cons]
              nlinarith

/-- Uniform bounds for all reached prefixes/suffixes, sufficient for held outputs. -/
theorem row_part_size (nBits : Bits) (adjacency low : Value) (mode : Mode)
    (targets part : List Bits) (hp : part.length ≤ targets.length) (out : Value)
    (hout : (row nBits adjacency low mode part).1=some out) : out.size ≤ 3*targets.length+1 :=
  (row_size nBits adjacency low mode part out hout).trans (by omega)

theorem matrix_part_size (nBits : Bits) (adjacency low : Value)
    (targets sources part : List Bits) (hp : part.length ≤ sources.length) (out : Value)
    (hout : (matrix nBits adjacency low targets part).1=some out) :
    out.size ≤ sources.length*(3*targets.length+2)+1 :=
  (matrix_size nBits adjacency low targets part out hout).trans (by gcongr)

private theorem vector_list {α : Type*} {m : ℕ} (v : Vector α m) :
    v.toList=(List.finRange m).map (fun i => v[i.val]) := by
  simpa only [Vector.toList_ofFn,List.finRange,List.map_ofFn,Function.comp_def] using
    congrArg Vector.toList (Vector.ofFn_getElem (xs := v)).symm

section Refinement
variable {n : ℕ} (D : EncodedUnitCostReplication.Input n)

/-- Finite descriptions only, used to state exact bytes already produced. -/
def adjacencyRowValue (source : Fin (3*n)) (targets : List (Fin (3*n))) : Value :=
  EncodedSequenceAccess.sequence (targets.map fun t => .flag (EncodedPortPreparation.portData D).adjacency[source.val][t.val])

def removalValue (targets : List (Fin (3*n))) : Value :=
  EncodedSequenceAccess.sequence (targets.map fun t => .flag (EncodedPortPreparation.portData D).removed[t.val])

def adjacencyValue (sources targets : List (Fin (3*n))) : Value :=
  EncodedSequenceAccess.sequence (sources.map fun s => adjacencyRowValue D s targets)

variable (nBits : Bits) (hn : value nBits=n)
variable (encode : Fin (3*n) → Bits) (he : ∀ i, value (encode i)=i.val)
include hn he

theorem adjacency_row_refines (source : Fin (3*n)) (targets : List (Fin (3*n))) :
    (row nBits (EncodedCellAccess.flagTable D.adjacency)
      (maskValue (EncodedPortPreparation.lowMask D)) (.adjacency (encode source))
      (targets.map encode)).1=some (adjacencyRowValue D source targets) := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      have hc := BinaryPortDecode.cell_refines D nBits (encode source) (encode target) hn source target
        (he source) (he target)
      simp only [List.map_cons,row,test,hc,ih,adjacencyRowValue,EncodedSequenceAccess.sequence]

theorem removal_row_refines (targets : List (Fin (3*n))) :
    (row nBits (EncodedCellAccess.flagTable D.adjacency)
      (maskValue (EncodedPortPreparation.lowMask D)) .removal (targets.map encode)).1=
      some (removalValue D targets) := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      have hc := BinaryPortDecode.removalCell_refines D nBits (encode target) hn target (he target)
      simp only [List.map_cons,row,test,hc,ih,removalValue,EncodedSequenceAccess.sequence]

theorem adjacency_matrix_refines (sources targets : List (Fin (3*n))) :
    (matrix nBits (EncodedCellAccess.flagTable D.adjacency)
      (maskValue (EncodedPortPreparation.lowMask D)) (targets.map encode) (sources.map encode)).1=
      some (adjacencyValue D sources targets) := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      simp only [List.map_cons,matrix,adjacency_row_refines D nBits hn encode he,ih,
        adjacencyValue,EncodedSequenceAccess.sequence]

omit hn he in
theorem adjacencyValue_native :
    adjacencyValue D (List.finRange (3*n)) (List.finRange (3*n))=
      EncodedCellAccess.flagTable (EncodedPortPreparation.portData D).adjacency := by
  unfold adjacencyValue EncodedCellAccess.flagTable
  rw [vector_list (EncodedPortPreparation.portData D).adjacency]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro s hs
  unfold adjacencyRowValue
  rw [vector_list (EncodedPortPreparation.portData D).adjacency[s.val]]
  simp only [List.map_map,Function.comp_def]

omit hn he in
theorem removalValue_native :
    removalValue D (List.finRange (3*n))=maskValue (EncodedPortPreparation.portData D).removed := by
  unfold removalValue maskValue
  rw [vector_list (EncodedPortPreparation.portData D).removed]
  simp only [List.map_map,Function.comp_def]

end Refinement

/-- Each scalar and traversal result is retained once. Optional malformed
results do not prevent the independent removal traversal from running. -/
structure Output where
  originalCount : Bits
  portCount : Bits
  vertices : List Bits
  adjacency : Option Value
  removed : Option Value
  operations : ℕ
  deriving DecidableEq, Repr

def build (nBits : Bits) (adjacency low : Value) : Output :=
  let t := triple nBits
  let vs := labels t.1 []
  let a := matrix nBits adjacency low vs.1 vs.1
  let r := row nBits adjacency low .removal vs.1
  ⟨nBits,t.1,vs.1,a.1,r.1,t.2+vs.2+a.2+r.2+20⟩

inductive BuildExec (nBits : Bits) (adjacency low : Value) : Output → Prop
  | make (vertices : List Bits) (a r : Option Value) (q s t : ℕ) :
      LabelsExec (triple nBits).1 [] vertices q →
      MatrixExec nBits adjacency low vertices vertices a s →
      RowExec nBits adjacency low .removal vertices r t →
      BuildExec nBits adjacency low ⟨nBits,(triple nBits).1,vertices,a,r,
        (triple nBits).2+q+s+t+20⟩

theorem build_exec (nBits : Bits) (adjacency low : Value) :
    BuildExec nBits adjacency low (build nBits adjacency low) :=
  .make _ _ _ _ _ _ (labels_exec (triple nBits).1 [])
    (matrix_exec nBits adjacency low (labels (triple nBits).1 []).1 (labels (triple nBits).1 []).1)
    (row_exec nBits adjacency low .removal (labels (triple nBits).1 []).1)

theorem BuildExec.result {nBits : Bits} {adjacency low : Value} {out : Output}
    (run : BuildExec nBits adjacency low out) : out=build nBits adjacency low := by
  cases run with
  | make vertices a r q s t hv ha hr =>
      have hvv := hv.result
      have hav := ha.result
      have hrv := hr.result
      simp only [build,← hvv.1,← hvv.2,← hav.1,← hav.2,← hrv.1,← hrv.2]

theorem build_originalCount (nBits : Bits) (adjacency low : Value) :
    (build nBits adjacency low).originalCount=nBits := rfl

theorem build_count (nBits : Bits) (adjacency low : Value) :
    value (build nBits adjacency low).portCount=3*value nBits := triple_value nBits

theorem build_vertices {n : ℕ} (nBits : Bits) (hn : value nBits=n) (adjacency low : Value) :
    (build nBits adjacency low).vertices=(List.finRange (3*n)).map (fun i => i.val.bits) :=
  portLabels_refines nBits hn

theorem build_refines {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (nBits : Bits) (hn : value nBits=n) :
    (build nBits (EncodedCellAccess.flagTable D.adjacency)
      (maskValue (EncodedPortPreparation.lowMask D))).adjacency=
        some (EncodedCellAccess.flagTable (EncodedPortPreparation.portData D).adjacency) ∧
    (build nBits (EncodedCellAccess.flagTable D.adjacency)
      (maskValue (EncodedPortPreparation.lowMask D))).removed=
        some (maskValue (EncodedPortPreparation.portData D).removed) := by
  have hv := portLabels_refines nBits hn
  change (labels (triple nBits).1 []).1=_ at hv
  have he' : ∀ i : Fin (3*n), value i.val.bits=i.val := fun i => value_bits i.val
  constructor
  · change (matrix nBits _ _ _ _).1=_
    rw [hv]
    exact (adjacency_matrix_refines D nBits hn (fun i => i.val.bits) he'
      (List.finRange (3*n)) (List.finRange (3*n))).trans (congrArg some (adjacencyValue_native D))
  · change (row nBits _ _ .removal _).1=_
    rw [hv]
    exact (removal_row_refines D nBits hn (fun i => i.val.bits) he'
      (List.finRange (3*n))).trans (congrArg some (removalValue_native D))

theorem build_prepared {n : ℕ} (A : Vector (Vector Bool n) n)
    (w c : BinaryFractionalRows.Row n) (nBits : Bits) (hn : value nBits=n) :
    (build nBits (EncodedCellAccess.flagTable A)
      (maskValue (BinaryPortWeightPreparation.prepare nBits w c).low)).adjacency=
        some (EncodedCellAccess.flagTable
          (EncodedPortPreparation.portData (BinaryUnitCostParameters.rawInput A w c)).adjacency) ∧
    (build nBits (EncodedCellAccess.flagTable A)
      (maskValue (BinaryPortWeightPreparation.prepare nBits w c).low)).removed=
        some (maskValue
          (EncodedPortPreparation.portData (BinaryUnitCostParameters.rawInput A w c)).removed) := by
  rw [BinaryPortWeightPreparation.prepare_low nBits hn A w c]
  exact build_refines (BinaryUnitCostParameters.rawInput A w c) nBits hn

def buildBound (n D : ℕ) : ℕ :=
  32*(D+3)+8+labelsBound (3*n) (D+2)+
    matrixBound n D (D+2) (3*n) (3*n)+rowBound n D (D+2) (3*n)+20

theorem build_bound {n : ℕ} (A : Vector (Vector Bool n) n) (low : Vector Bool n)
    (nBits : Bits) (hn : value nBits=n) (D : ℕ) (hD : nBits.length ≤ D) :
    (build nBits (EncodedCellAccess.flagTable A) (maskValue low)).operations ≤ buildBound n D := by
  have hv := portLabels_bounds nBits hn D hD
  have hw := hv.2.1
  change ∀ word∈(labels (triple nBits).1 []).1, word.length ≤ D+2 at hw
  have ha := matrix_bound A low nBits (labels (triple nBits).1 []).1
    (labels (triple nBits).1 []).1 D (D+2) hD hw hw
  have hr := row_bound A low nBits .removal (labels (triple nBits).1 []).1 D (D+2) hD trivial hw
  have hl := hv.1
  change (labels (triple nBits).1 []).1.length=3*n at hl
  rw [hl] at ha hr
  have hq := hv.2.2
  change (triple nBits).2+(labels (triple nBits).1 []).2+4 ≤ _ at hq
  unfold build buildBound
  dsimp only
  omega

theorem build_shapes {n : ℕ} (nBits : Bits) (hn : value nBits=n)
    (adjacency low : Value) (D : ℕ) (hD : nBits.length ≤ D) :
    (build nBits adjacency low).portCount.length ≤ D+2 ∧
    (build nBits adjacency low).vertices.length=3*n ∧
    (labelValue (build nBits adjacency low).vertices).size ≤ 3*n*(D+4)+1 ∧
    (∀ a, (build nBits adjacency low).adjacency=some a → a.size ≤ (3*n)*(9*n+2)+1) ∧
    (∀ r, (build nBits adjacency low).removed=some r → r.size ≤ 9*n+1) := by
  have hv := portLabels_bounds nBits hn D hD
  have hl := hv.1
  change (labels (triple nBits).1 []).1.length=3*n at hl
  have hs := labelValue_size hv.2.1
  change (labelValue (labels (triple nBits).1 []).1).size ≤
    (labels (triple nBits).1 []).1.length*(D+2+2)+1 at hs
  rw [hl] at hs
  refine ⟨triple_width nBits D hD,hl,?_,?_,?_⟩
  · simpa only [build,Nat.add_assoc] using hs
  · intro a ha
    have hh := matrix_size nBits adjacency low (labels (triple nBits).1 []).1
      (labels (triple nBits).1 []).1 a ha
    rw [hl] at hh
    convert hh using 1; ring
  · intro r hr
    have hh := row_size nBits adjacency low .removal (labels (triple nBits).1 []).1 r hr
    rw [hl] at hh
    convert hh using 1; ring

end DirectedFlowCutGap.BinaryPortMaterialization
