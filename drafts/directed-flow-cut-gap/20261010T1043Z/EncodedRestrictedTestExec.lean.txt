import DirectedFlowCutGap.EncodedCellAccess
import DirectedFlowCutGap.EncodedShortcutReachability

/-!
# Closed encoded execution of the restricted shortcut adjacency test

The actual body receives retained representations and stored binary labels. It
reads the adjacency cell, then short-circuits the two endpoint-or-removal tests.
Every reached sequence read copies its selected value; numeric equality uses
the named binary comparator even for padded labels. The execution constructors
admit only these fixed primitives and Boolean branches, never an arbitrary
host function, equality dictionary, or callback at unit charge.

Representation maps below are proof-side descriptions of already retained
arrays. Their construction, the enclosing CountedSearch loop and the global
representation-overhead theorem remain separate joins. This leaf supplies an
exact result and polynomial local charge for replacing restrictedTest's word
annotation; it does not claim that the annotation 24 is a bit-operation bound.
-/
namespace DirectedFlowCutGap.EncodedRestrictedTestExec
open BinaryArithmetic EncodedSequenceAccess

/-- A fixed tag test, shared by the one-read and two-read flag bodies. -/
def asFlag : Option Value → Option Bool
  | some (.flag b) => some b
  | _ => none

def maskValue {m : ℕ} (mask : Vector Bool m) : Value :=
  sequence (mask.toList.map Value.flag)

def flagAt (i : Bits) (mask : Value) : Option Bool × ℕ :=
  let r := read i mask
  (asFlag r.1,r.2+4)

inductive FlagAtExec (i : Bits) (mask : Value) : Option Bool → ℕ → Prop
  | readFlag (v : Option Value) (q : ℕ) :
      ReadExec i mask v q → FlagAtExec i mask (asFlag v) (q+4)

inductive FlagCellExec (i j : Bits) (table : Value) : Option Bool → ℕ → Prop
  | readFlag (v : Option Value) (q : ℕ) :
      Read2Exec i j table v q → FlagCellExec i j table (asFlag v) (q+4)

private theorem read2_result {i j : Bits} {table : Value} {out : Option Value} {q : ℕ}
    (h : Read2Exec i j table out q) : out=(read2 i j table).1 ∧ q=(read2 i j table).2 := by
  cases h with
  | missing q hr =>
      have hh := hr.result
      constructor <;> simp only [read2,← hh.1,← hh.2]
  | found row cell q r hr hc =>
      have hh := hr.result
      have ht := hc.result
      constructor <;> simp only [read2,← hh.1,← hh.2,← ht.1,← ht.2]

theorem FlagAtExec.result {i : Bits} {mask : Value} {out : Option Bool} {q : ℕ}
    (h : FlagAtExec i mask out q) : out=(flagAt i mask).1 ∧ q=(flagAt i mask).2 := by
  cases h with
  | readFlag v q hr =>
      have hh := hr.result
      constructor <;> simp only [flagAt,← hh.1,← hh.2]

theorem FlagCellExec.result {i j : Bits} {table : Value} {out : Option Bool} {q : ℕ}
    (h : FlagCellExec i j table out q) :
    out=(EncodedCellAccess.flag i j table).1 ∧ q=(EncodedCellAccess.flag i j table).2 := by
  cases h with
  | readFlag v q hr =>
      have hh := read2_result hr
      constructor
      · simp only [EncodedCellAccess.flag,← hh.1,asFlag]
        cases v with
        | none => rfl
        | some v => cases v <;> rfl
      · simp only [EncodedCellAccess.flag,← hh.2]

theorem flagAt_exec (i : Bits) (mask : Value) :
    FlagAtExec i mask (flagAt i mask).1 (flagAt i mask).2 :=
  .readFlag _ _ (read_exec i mask)

theorem flagCell_exec (i j : Bits) (table : Value) :
    FlagCellExec i j table (EncodedCellAccess.flag i j table).1
      (EncodedCellAccess.flag i j table).2 := by
  have he : asFlag (read2 i j table).1=(EncodedCellAccess.flag i j table).1 := by
    change asFlag (read2 i j table).1 =
      match (read2 i j table).1 with | some (.flag b) => some b | _ => none
    cases (read2 i j table).1 with
    | none => rfl
    | some v => cases v <;> rfl
  rw [← he]
  exact FlagCellExec.readFlag _ _ (read2_exec i j table)

theorem flagAt_get {m : ℕ} (mask : Vector Bool m) (i : Fin m) (ib : Bits)
    (hi : value ib=i.val) : (flagAt ib (maskValue mask)).1=some mask[i.val] := by
  have hr := read_get ib (mask.toList.map Value.flag)
  simp [flagAt,maskValue,hr,hi,asFlag]

theorem flagAt_bound {m : ℕ} (mask : Vector Bool m) (ib : Bits) (B : ℕ)
    (hi : ib.length ≤ B) :
    (flagAt ib (maskValue mask)).2 ≤ 20*(m+1)*(B+1)+12 := by
  have hr := read_bound ib (mask.toList.map Value.flag) B 2 hi (by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    rfl)
  simpa [flagAt,maskValue,Nat.add_assoc] using
    Nat.add_le_add_right hr 4

/-- The mask is read only when the stored endpoint labels differ numerically. -/
def endpoint (i s : Bits) (mask : Value) : Option Bool × ℕ :=
  let c := BinaryArithmetic.compare i s
  if c.equal then (some true,c.steps+4) else
    let r := flagAt i mask
    (r.1,c.steps+r.2+8)

inductive EndpointExec (i s : Bits) (mask : Value) : Option Bool → ℕ → Prop
  | equal : (BinaryArithmetic.compare i s).equal=true →
      EndpointExec i s mask (some true) ((BinaryArithmetic.compare i s).steps+4)
  | removed (out : Option Bool) (q : ℕ) :
      (BinaryArithmetic.compare i s).equal=false → FlagAtExec i mask out q →
      EndpointExec i s mask out ((BinaryArithmetic.compare i s).steps+q+8)

theorem EndpointExec.result {i s : Bits} {mask : Value} {out : Option Bool} {q : ℕ}
    (h : EndpointExec i s mask out q) : out=(endpoint i s mask).1 ∧ q=(endpoint i s mask).2 := by
  cases h with
  | equal he => constructor <;> simp only [endpoint,he,ite_true]
  | removed out q he hr =>
      have hh := hr.result
      constructor <;> simp only [endpoint,he,Bool.false_eq_true,ite_false,← hh.1,← hh.2]

theorem endpoint_exec (i s : Bits) (mask : Value) :
    EndpointExec i s mask (endpoint i s mask).1 (endpoint i s mask).2 := by
  cases he : (BinaryArithmetic.compare i s).equal with
  | true => simpa only [endpoint,he,ite_true] using EndpointExec.equal (mask := mask) he
  | false =>
      simpa only [endpoint,he,Bool.false_eq_true,ite_false] using
        EndpointExec.removed (i := i) (s := s) (mask := mask) _ _ he (flagAt_exec i mask)

theorem endpoint_get {m : ℕ} (mask : Vector Bool m) (i s : Fin m) (ib sb : Bits)
    (hi : value ib=i.val) (hs : value sb=s.val) :
    (endpoint ib sb (maskValue mask)).1=some (decide (i=s) || mask[i.val]) := by
  have he : (BinaryArithmetic.compare ib sb).equal=decide (i=s) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [hi,hs,Bool.decide_coe,decide_eq_true_eq,Fin.ext_iff] using
      (BinaryArithmetic.compare_spec ib sb).2.1
  have hr := flagAt_get mask i ib hi
  by_cases h : i=s <;> simp [endpoint,he,h,hr]

def endpointBound (m B : ℕ) : ℕ := 20*(m+1)*(B+1)+16*(B+1)+20

theorem endpoint_bound {m : ℕ} (mask : Vector Bool m) (ib sb : Bits) (B : ℕ)
    (hi : ib.length ≤ B) (hs : sb.length ≤ B) :
    (endpoint ib sb (maskValue mask)).2 ≤ endpointBound m B := by
  have hc := (BinaryArithmetic.compare_spec ib sb).2.2
  have hmax : max ib.length sb.length ≤ B := max_le hi hs
  have hr := flagAt_bound mask ib B hi
  unfold endpoint endpointBound
  dsimp only
  split <;> dsimp only <;> omega

/-- Short-circuit adjacency, left endpoint/removal, then right endpoint/removal.
Malformed retained representations propagate `none` honestly. -/
def test (s t u v : Bits) (adjacency removed : Value) : Option Bool × ℕ :=
  let a := EncodedCellAccess.flag u v adjacency
  match a.1 with
  | none => (none,a.2+4)
  | some false => (some false,a.2+4)
  | some true =>
      let l := endpoint u s removed
      match l.1 with
      | none => (none,a.2+l.2+8)
      | some false => (some false,a.2+l.2+8)
      | some true =>
          let r := endpoint v t removed
          (r.1,a.2+l.2+r.2+12)

inductive RestrictedTestExec (s t u v : Bits) (adjacency removed : Value) :
    Option Bool → ℕ → Prop
  | missingAdj (q : ℕ) : FlagCellExec u v adjacency none q →
      RestrictedTestExec s t u v adjacency removed none (q+4)
  | falseAdj (q : ℕ) : FlagCellExec u v adjacency (some false) q →
      RestrictedTestExec s t u v adjacency removed (some false) (q+4)
  | missingLeft (q r : ℕ) : FlagCellExec u v adjacency (some true) q →
      EndpointExec u s removed none r →
      RestrictedTestExec s t u v adjacency removed none (q+r+8)
  | falseLeft (q r : ℕ) : FlagCellExec u v adjacency (some true) q →
      EndpointExec u s removed (some false) r →
      RestrictedTestExec s t u v adjacency removed (some false) (q+r+8)
  | right (out : Option Bool) (q r k : ℕ) : FlagCellExec u v adjacency (some true) q →
      EndpointExec u s removed (some true) r → EndpointExec v t removed out k →
      RestrictedTestExec s t u v adjacency removed out (q+r+k+12)

theorem RestrictedTestExec.result {s t u v : Bits} {a z : Value}
    {out : Option Bool} {q : ℕ} (h : RestrictedTestExec s t u v a z out q) :
    out=(test s t u v a z).1 ∧ q=(test s t u v a z).2 := by
  cases h with
  | missingAdj q ha =>
      have a := ha.result
      constructor <;> simp only [test,← a.1,← a.2]
  | falseAdj q ha =>
      have a := ha.result
      constructor <;> simp only [test,← a.1,← a.2]
  | missingLeft q r ha hl =>
      have a := ha.result
      have l := hl.result
      constructor <;> simp only [test,← a.1,← a.2,← l.1,← l.2]
  | falseLeft q r ha hl =>
      have a := ha.result
      have l := hl.result
      constructor <;> simp only [test,← a.1,← a.2,← l.1,← l.2]
  | right out q r k ha hl hr =>
      have a := ha.result
      have l := hl.result
      have r := hr.result
      constructor <;> simp only [test,← a.1,← a.2,← l.1,← l.2,← r.1,← r.2]

theorem test_exec (s t u v : Bits) (adjacency removed : Value) :
    RestrictedTestExec s t u v adjacency removed
      (test s t u v adjacency removed).1 (test s t u v adjacency removed).2 := by
  have ha := flagCell_exec u v adjacency
  cases hea : (EncodedCellAccess.flag u v adjacency).1 with
  | none =>
      rw [hea] at ha
      simpa only [test,hea] using
        RestrictedTestExec.missingAdj (s := s) (t := t) (removed := removed) _ ha
  | some b =>
      cases b with
      | false =>
          rw [hea] at ha
          simpa only [test,hea] using
            RestrictedTestExec.falseAdj (s := s) (t := t) (removed := removed) _ ha
      | true =>
          rw [hea] at ha
          have hl := endpoint_exec u s removed
          cases hel : (endpoint u s removed).1 with
          | none =>
              rw [hel] at hl
              simpa only [test,hea,hel] using
                RestrictedTestExec.missingLeft (t := t) _ _ ha hl
          | some c =>
              cases c with
              | false =>
                  rw [hel] at hl
                  simpa only [test,hea,hel] using
                    RestrictedTestExec.falseLeft (t := t) _ _ ha hl
              | true =>
                  rw [hel] at hl
                  simpa only [test,hea,hel] using
                    RestrictedTestExec.right _ _ _ _ ha hl (endpoint_exec v t removed)

theorem test_get {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (s t u v : Fin m) (sb tb ub vb : Bits)
    (hs : value sb=s.val) (ht : value tb=t.val)
    (hu : value ub=u.val) (hv : value vb=v.val) :
    (test sb tb ub vb (EncodedCellAccess.flagTable D.adjacency) (maskValue D.removed)).1 =
      some (D.restrictedBool s t u v) := by
  have ha := EncodedCellAccess.flag_get D.adjacency u v ub vb hu hv
  have hl := endpoint_get D.removed u s ub sb hu hs
  have hr := endpoint_get D.removed v t vb tb hv ht
  simp only [test,ha,hl,hr,EncodedShortcutReachability.Input.restrictedBool]
  cases D.adjacency[u.val][v.val] <;>
    cases (decide (u=s) || D.removed[u.val]) <;> rfl

/-- Exact decision-result bridge to the frozen counted-search callback. -/
theorem restrictedTest_refines {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (s t u v : Fin m) (sb tb ub vb : Bits)
    (hs : value sb=s.val) (ht : value tb=t.val)
    (hu : value ub=u.val) (hv : value vb=v.val) :
    (test sb tb ub vb (EncodedCellAccess.flagTable D.adjacency) (maskValue D.removed)).1 =
      some (@decide ((D.restrictedGraph s t).Adj u v) (D.restrictedTest s t u v).1) := by
  have he : @decide ((D.restrictedGraph s t).Adj u v) (D.restrictedTest s t u v).1 =
      D.restrictedBool s t u v := by
    change @decide (D.restrictedBool s t u v=true) _ = D.restrictedBool s t u v
    exact @Bool.decide_eq_true (D.restrictedBool s t u v) (D.restrictedTest s t u v).1
  rw [he]
  exact test_get D s t u v sb tb ub vb hs ht hu hv

def testBound (m B : ℕ) : ℕ := read2Bound m m B 2+2*endpointBound m B+16

theorem test_bound {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (s t u v : Bits) (B : ℕ)
    (hs : s.length ≤ B) (ht : t.length ≤ B)
    (hu : u.length ≤ B) (hv : v.length ≤ B) :
    (test s t u v (EncodedCellAccess.flagTable D.adjacency) (maskValue D.removed)).2 ≤
      testBound m B := by
  have ha := EncodedCellAccess.flag_bound D.adjacency u v B hu hv
  have hl := endpoint_bound D.removed u s B hu hs
  have hr := endpoint_bound D.removed v t B hv ht
  unfold test testBound
  dsimp only
  split <;> (try dsimp only)
  · omega
  · omega
  · split <;> (try dsimp only) <;> omega

theorem maskValue_size {m : ℕ} (mask : Vector Bool m) :
    (maskValue mask).size ≤ 3*m+1 := by
  have h := sequence_size_bound (xs := mask.toList.map Value.flag) (S := 2) (by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    rfl)
  simpa [maskValue,Nat.mul_comm] using h

/-- A read can copy a full row, and the retained table itself is quadratic. -/
theorem flagTable_size {m : ℕ} (adjacency : Vector (Vector Bool m) m) :
    (EncodedCellAccess.flagTable adjacency).size ≤ m*(3*m+2)+1 := by
  have h := sequence_size_bound
    (xs := adjacency.toList.map (fun row => sequence (row.toList.map Value.flag)))
    (S := 3*m+1) (by
      intro x hx
      obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hx
      exact maskValue_size row)
  simpa [EncodedCellAccess.flagTable,Nat.add_assoc] using h

end DirectedFlowCutGap.EncodedRestrictedTestExec
