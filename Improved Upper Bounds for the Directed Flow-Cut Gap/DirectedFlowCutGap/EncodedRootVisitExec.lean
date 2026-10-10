import DirectedFlowCutGap.EncodedSearchScanExec
import DirectedFlowCutGap.CountedSearchRootProjection

/-!
# Closed root-only visit for the actual shortcut search

The two concrete scans use the fixed numeric-equality and restricted-adjacency
modes. The visit inspects only their found tags, and, when a new root is reached,
copies its stored label and prepends one entry with an empty payload. The
projection theorem connects this exact body to the original counted visit's
root table; no dependent path payload is constructed or evaluated.

This local source-body certificate does not yet cover the pass/round loops,
initial representation construction or movement of retained argument frames.
Those remain required for a complete bit-cost theorem.
-/
namespace DirectedFlowCutGap.EncodedRootVisitExec
open BinaryArithmetic EncodedSequenceAccess EncodedSearchScanExec

structure Input where
  source : Bits
  target : Bits
  adjacency : Value
  removed : Value

def Input.mode (D : Input) (vertex : Bits) : Mode :=
  .restricted D.source D.target vertex D.adjacency D.removed

def foundScan (mode : Mode) (table : List Entry) : Option Bool × ℕ :=
  let r := EncodedSearchScanExec.scan mode table
  (r.1.map Option.isSome,r.2+4)

inductive FoundExec (mode : Mode) (table : List Entry) : Option Bool → ℕ → Prop
  | scan (out : Option (Option Entry)) (q : ℕ) :
      ScanExec mode table out q → FoundExec mode table (out.map Option.isSome) (q+4)

theorem foundScan_exec (mode : Mode) (table : List Entry) :
    FoundExec mode table (foundScan mode table).1 (foundScan mode table).2 :=
  .scan _ _ (scan_exec mode table)

theorem FoundExec.result {mode : Mode} {table : List Entry} {out : Option Bool} {q : ℕ}
    (h : FoundExec mode table out q) : out=(foundScan mode table).1 ∧ q=(foundScan mode table).2 := by
  cases h with
  | scan out q hr =>
      have h := hr.result
      constructor <;> simp only [foundScan,← h.1,← h.2]

def visit (D : Input) (table : List Entry) (vertex : Bits) : Option (List Entry) × ℕ :=
  let r := foundScan (.lookup vertex) table
  match r.1 with
  | none => (none,r.2+4)
  | some true => (some table,r.2+4)
  | some false =>
      let a := foundScan (D.mode vertex) table
      match a.1 with
      | none => (none,r.2+a.2+8)
      | some false => (some table,r.2+a.2+8)
      | some true =>
          let c := copyBits vertex
          (some (keyEntry c.1::table),r.2+a.2+c.2+16)

inductive VisitExec (D : Input) (table : List Entry) (vertex : Bits) :
    Option (List Entry) → ℕ → Prop
  | missingLookup (q : ℕ) : FoundExec (.lookup vertex) table none q →
      VisitExec D table vertex none (q+4)
  | oldRoot (q : ℕ) : FoundExec (.lookup vertex) table (some true) q →
      VisitExec D table vertex (some table) (q+4)
  | missingAdjacency (q r : ℕ) : FoundExec (.lookup vertex) table (some false) q →
      FoundExec (D.mode vertex) table none r → VisitExec D table vertex none (q+r+8)
  | noPredecessor (q r : ℕ) : FoundExec (.lookup vertex) table (some false) q →
      FoundExec (D.mode vertex) table (some false) r →
      VisitExec D table vertex (some table) (q+r+8)
  | newRoot (out : Bits) (q r k : ℕ) : FoundExec (.lookup vertex) table (some false) q →
      FoundExec (D.mode vertex) table (some true) r → BitsCopyExec vertex out k →
      VisitExec D table vertex (some (keyEntry out::table)) (q+r+k+16)

theorem VisitExec.result {D : Input} {table : List Entry} {vertex : Bits}
    {out : Option (List Entry)} {q : ℕ} (h : VisitExec D table vertex out q) :
    out=(visit D table vertex).1 ∧ q=(visit D table vertex).2 := by
  cases h with
  | missingLookup q hr =>
      have r := hr.result
      constructor <;> simp only [visit,← r.1,← r.2]
  | oldRoot q hr =>
      have r := hr.result
      constructor <;> simp only [visit,← r.1,← r.2]
  | missingAdjacency q r hr ha =>
      have h := hr.result
      have a := ha.result
      constructor <;> simp only [visit,← h.1,← h.2,← a.1,← a.2]
  | noPredecessor q r hr ha =>
      have h := hr.result
      have a := ha.result
      constructor <;> simp only [visit,← h.1,← h.2,← a.1,← a.2]
  | newRoot out q r k hr ha hc =>
      have h := hr.result
      have a := ha.result
      have c := hc.result
      constructor <;> simp only [visit,← h.1,← h.2,← a.1,← a.2,← c.1,← c.2]

theorem visit_exec (D : Input) (table : List Entry) (vertex : Bits) :
    VisitExec D table vertex (visit D table vertex).1 (visit D table vertex).2 := by
  have hr := foundScan_exec (.lookup vertex) table
  cases he : (foundScan (.lookup vertex) table).1 with
  | none =>
      rw [he] at hr
      simpa only [visit,he] using VisitExec.missingLookup (D := D) _ hr
  | some b =>
      cases b with
      | true =>
          rw [he] at hr
          simpa only [visit,he] using VisitExec.oldRoot (D := D) _ hr
      | false =>
          rw [he] at hr
          have ha := foundScan_exec (D.mode vertex) table
          cases hae : (foundScan (D.mode vertex) table).1 with
          | none =>
              rw [hae] at ha
              simpa only [visit,he,hae] using VisitExec.missingAdjacency _ _ hr ha
          | some a =>
              cases a with
              | false =>
                  rw [hae] at ha
                  simpa only [visit,he,hae] using VisitExec.noPredecessor _ _ hr ha
              | true =>
                  rw [hae] at ha
                  simpa only [visit,he,hae] using
                    VisitExec.newRoot _ _ _ _ hr ha (copyBits_exec vertex)

/-- Proof-side representation of already retained graph and endpoint data. -/
def inputValue {m : ℕ} (D : EncodedShortcutReachability.Input m) (s t : Bits) : Input :=
  ⟨s,t,EncodedCellAccess.flagTable D.adjacency,EncodedRestrictedTestExec.maskValue D.removed⟩

def tableValue {m : ℕ} (encode : Fin m → Bits) (roots : List (Fin m)) : List Entry :=
  roots.map (fun v => keyEntry (encode v))

theorem lookup_found {m : ℕ} (encode : Fin m → Bits)
    (he : ∀ v, value (encode v)=v.val) (roots : List (Fin m)) (v : Fin m) :
    (foundScan (.lookup (encode v)) (tableValue encode roots)).1 =
      some (roots.any (fun u => decide (u=v))) := by
  apply scan_found
  intro u hu
  have h : (BinaryArithmetic.compare (encode u) (encode v)).equal=decide (u=v) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [he,decide_eq_true_eq,Fin.ext_iff] using
      (BinaryArithmetic.compare_spec (encode u) (encode v)).2.1
  simp only [check,keyEntry,h]

theorem adjacency_found {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val)
    (roots : List (Fin m)) (s t v : Fin m) :
    (foundScan ((inputValue D (encode s) (encode t)).mode (encode v))
      (tableValue encode roots)).1 =
      some (roots.any (fun u => decide ((D.restrictedGraph s t).Adj v u))) := by
  apply scan_found
  intro u hu
  have h := EncodedRestrictedTestExec.test_get D s t v u
    (encode s) (encode t) (encode v) (encode u) (he s) (he t) (he v) (he u)
  have hb : decide ((D.restrictedGraph s t).Adj v u) = D.restrictedBool s t v u := by
    change decide (D.restrictedBool s t v u = true) = D.restrictedBool s t v u
    exact Bool.decide_eq_true
  simpa only [check,Input.mode,inputValue,keyEntry,hb] using h

/-- Exact roots and their original stored padding, on every represented input. -/
theorem visit_refines {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val)
    (roots : List (Fin m)) (s t v : Fin m) :
    (visit (inputValue D (encode s) (encode t)) (tableValue encode roots) (encode v)).1 =
      some (tableValue encode (CountedSearchRootProjection.visit
        (fun u w => decide ((D.restrictedGraph s t).Adj u w)) roots v)) := by
  have hl := lookup_found encode he roots v
  have ha := adjacency_found D encode he roots s t v
  simp only [visit,hl,ha,CountedSearchRootProjection.visit]
  cases roots.any (fun u => decide (u=v)) <;>
    cases roots.any (fun u => decide ((D.restrictedGraph s t).Adj v u)) <;>
    simp [tableValue,(copyBits_spec (encode v)).1]

def visitBound (m B : ℕ) : ℕ :=
  scanBound m (16*(B+1)+4) B 1+
    scanBound m (EncodedRestrictedTestExec.testBound m B+4) B 1+4*B+25

theorem visit_bound {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (encode : Fin m → Bits) (roots : List (Fin m)) (s t v : Fin m) (B : ℕ)
    (he : ∀ v, (encode v).length ≤ B) (hlen : roots.length ≤ m) :
    (visit (inputValue D (encode s) (encode t)) (tableValue encode roots) (encode v)).2 ≤
      visitBound m B := by
  have hl := keyOnly_bound (.lookup (encode v)) (roots.map encode)
    (16*(B+1)+4) B
    (by
      intro label hlabel
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hlabel
      exact lookup_check_bound (encode u) (encode v) B (he u) (he v))
    (by
      intro label hlabel
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hlabel
      exact he u)
  have ha := keyOnly_bound ((inputValue D (encode s) (encode t)).mode (encode v))
    (roots.map encode) (EncodedRestrictedTestExec.testBound m B+4) B
    (by
      intro label hlabel
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hlabel
      exact restricted_check_bound D (encode s) (encode t) (encode v) (encode u)
        B (he s) (he t) (he v) (he u))
    (by
      intro label hlabel
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hlabel
      exact he u)
  simp only [List.map_map,Function.comp_def,List.length_map] at hl ha
  have hc := (copyBits_spec (encode v)).2
  have hw := he v
  have lm := Nat.mul_le_mul_right (16*(B+1)+4+12) hlen
  have am := Nat.mul_le_mul_right (EncodedRestrictedTestExec.testBound m B+4+12) hlen
  unfold visit foundScan tableValue
  try dsimp only
  split <;> (try dsimp only)
  · unfold visitBound scanBound at *
    omega
  · unfold visitBound scanBound at *
    omega
  · split <;> (try dsimp only) <;> unfold visitBound scanBound at * <;> omega

end DirectedFlowCutGap.EncodedRootVisitExec
