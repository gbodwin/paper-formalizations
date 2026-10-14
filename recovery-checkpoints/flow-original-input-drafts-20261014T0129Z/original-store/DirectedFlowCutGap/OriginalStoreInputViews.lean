import DirectedFlowCutGap.RowVerticesLabels
import DirectedFlowCutGap.DemandCollectionRefinement

/-!
UNVERIFIED ADDITIVE DRAFT, 2026-10-14. No Lean compilation has been run.

Charged typed-input views. `advance` uses the published Boolean increment body;
its natural counter is structural recursion on an already supplied typed index.
This is a declared Boolean/list cost model, not a finite-instruction parser,
serialization decoder, or statement about native Lean execution time.
The conversion from external data to the typed Vector/Fin inputs is excluded.
-/
namespace DirectedFlowCutGap.OriginalStoreInputViews
open BinaryArithmetic BinaryRational

/-- Produce an index word by actual repeated binary increment. The natural
index controls structural recursion; no natural decoding computes an address. -/
def advance : ℕ → Bits → Bits × ℕ
  | 0, acc => (acc, 4)
  | k+1, acc =>
      let a := increment true acc
      let r := advance k a.1
      (r.1, a.2+r.2+8)

theorem advance_bound (k : ℕ) (acc : Bits) :
    (advance k acc).1.length ≤ acc.length+k ∧
    (advance k acc).2 ≤ 16*(k+1)*(acc.length+k+1) := by
  induction k generalizing acc with
  | zero => simp [advance]; omega
  | succ k ih =>
      have hi := increment_spec true acc
      obtain ⟨hw,hq⟩ := ih (increment true acc).1
      simp only [advance]
      constructor
      · omega
      · have shifted : (increment true acc).1.length+k+1 ≤ acc.length+k+2 := by omega
        have charge := hq.trans (Nat.mul_le_mul_left (16*(k+1)) shifted)
        nlinarith

/-- Literal equality of the padded word, not merely equality of its value. -/
theorem advance_get (k n : ℕ) (acc : Bits) (h : k<n) :
    (advance k acc).1=
      (RowVertexScan.words n acc)[k]'(by rw [RowVertexScan.words_length];exact h) := by
  induction k generalizing n acc with
  | zero =>
      cases n with
      | zero => omega
      | succ n => rfl
  | succ k ih =>
      cases n with
      | zero => omega
      | succ n =>
          simpa only [advance,RowVertexScan.words,List.getElem_cons_succ] using
            ih n (increment true acc).1 (by omega)

theorem advance_label {n : ℕ} (i : Fin n) :
    (advance i.val []).1=RowVertices.vertexLabel i :=
  advance_get i.val n [] i.isLt

def demandFields {n : ℕ} : List (BinaryFractionalWalkOracle.Pair n) →
    List (Bits × Bits) × ℕ
  | [] => ([],4)
  | d::ds =>
      let a := advance d.1.val []
      let b := advance d.2.val []
      let r := demandFields ds
      ((a.1,b.1)::r.1,a.2+b.2+r.2+12)

theorem demandFields_exact {n : ℕ} (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    (demandFields ds).1=
      ds.map (fun d => (RowVertices.vertexLabel d.1,RowVertices.vertexLabel d.2)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [demandFields,List.map_cons,advance_label,ih]

theorem demandFields_charge {n : ℕ} (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    (demandFields ds).2 ≤ ds.length*(32*(n+1)^2+12)+4 := by
  induction ds with
  | nil => simp [demandFields]
  | cons d ds ih =>
      have ha := (advance_bound d.1.val []).2
      have hb := (advance_bound d.2.val []).2
      have h1 := d.1.isLt
      have h2 := d.2.isLt
      have qa : (advance d.1.val []).2 ≤ 16*(n+1)^2 := by
        simp only [List.length_nil,Nat.zero_add] at ha
        calc
          (advance d.1.val []).2 ≤ 16*(d.1.val+1)*(d.1.val+1) := ha
          _ ≤ 16*(n+1)^2 := by
            simp only [pow_two,Nat.mul_assoc]
            gcongr <;> omega
      have qb : (advance d.2.val []).2 ≤ 16*(n+1)^2 := by
        simp only [List.length_nil,Nat.zero_add] at hb
        calc
          (advance d.2.val []).2 ≤ 16*(d.2.val+1)*(d.2.val+1) := hb
          _ ≤ 16*(n+1)^2 := by
            simp only [pow_two,Nat.mul_assoc]
            gcongr <;> omega
      simp only [demandFields,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

/-- These are views of the original stored fields: no normalization is applied. -/
def costFields {n : ℕ} (costs : BinaryFractionalRows.Row n) : List (Bits × Bits) × ℕ :=
  (IndexedRationalRead.fields costs.toList,8*costs.toList.length+4)

/-- Declared vector/list-view allowance includes every matrix cell. -/
def matrixFields {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) :
    List Bits × ℕ :=
  let rows := GraphRelaxationRefinement.matrix adjacency
  (rows,8*rows.length+8*(rows.map List.length).sum+4)

/-- The field and matrix views carry structural list/record allowances. They
are NOT machine traces or claims about the compiler's Vector implementation. -/
def viewCharge {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  (costFields costs).2+(matrixFields adjacency).2+(demandFields ds).2

end DirectedFlowCutGap.OriginalStoreInputViews
