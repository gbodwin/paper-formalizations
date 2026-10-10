import DirectedFlowCutGap.EncodedRestrictedTestExec

/-!
# Closed first-hit scans for the actual counted-search predicates

The body has exactly two fixed modes: binary key equality and the restricted
adjacency test. It traverses already retained entries in order, copying the
complete first matching entry with the certified bit/value copy bodies. There
is no arbitrary executable predicate, encoding function or equality callback.
Outer `none` reports a malformed restricted-test representation; `some none`
is an ordinary completed scan with no matching entry.

The relation to CountedSearch.scan uses encoding maps only as mathematical
observations. It does not execute them or claim their construction is free.
The enclosing search must still construct a finite representation of each
actual dependent path record and establish the payload-size invariant. No
host path function is evaluated by this leaf or assigned unit cost.
-/
namespace DirectedFlowCutGap.EncodedSearchScanExec
open BinaryArithmetic EncodedSequenceAccess
open IntegralNetworkFlow.Tabulated

structure Entry where
  label : Bits
  payload : Value
  deriving DecidableEq, Repr

inductive Mode where
  | lookup (target : Bits)
  | restricted (source target vertex : Bits) (adjacency removed : Value)

/-- These are the only two callable predicate bodies. -/
def check : Mode → Bits → Option Bool × ℕ
  | .lookup target, label =>
      let r := BinaryArithmetic.compare label target
      (some r.equal,r.steps+4)
  | .restricted s t u adjacency removed, label =>
      let r := EncodedRestrictedTestExec.test s t u label adjacency removed
      (r.1,r.2+4)

inductive CheckExec : Mode → Bits → Option Bool → ℕ → Prop
  | lookup (target label : Bits) :
      CheckExec (.lookup target) label (some (BinaryArithmetic.compare label target).equal)
        ((BinaryArithmetic.compare label target).steps+4)
  | restricted (s t u label : Bits) (adjacency removed : Value) (out : Option Bool) (q : ℕ) :
      EncodedRestrictedTestExec.RestrictedTestExec s t u label adjacency removed out q →
      CheckExec (.restricted s t u adjacency removed) label out (q+4)

theorem check_exec (mode : Mode) (label : Bits) :
    CheckExec mode label (check mode label).1 (check mode label).2 := by
  cases mode with
  | lookup target => exact .lookup target label
  | restricted s t u adjacency removed =>
      exact .restricted s t u label adjacency removed _ _
        (EncodedRestrictedTestExec.test_exec s t u label adjacency removed)

theorem CheckExec.result {mode : Mode} {label : Bits} {out : Option Bool} {q : ℕ}
    (h : CheckExec mode label out q) : out=(check mode label).1 ∧ q=(check mode label).2 := by
  cases h with
  | lookup target label => exact ⟨rfl,rfl⟩
  | restricted s t u label adjacency removed out q hr =>
      have hh := hr.result
      exact ⟨hh.1,congrArg (fun k => k+4) hh.2⟩

def copyEntry (e : Entry) : Entry × ℕ :=
  let l := EncodedSequenceAccess.copyBits e.label
  let p := EncodedSequenceAccess.copy e.payload
  (⟨l.1,p.1⟩,l.2+p.2+8)

inductive CopyEntryExec (e : Entry) : Entry → ℕ → Prop
  | copy (label : Bits) (payload : Value) (q r : ℕ) :
      BitsCopyExec e.label label q → CopyExec e.payload payload r →
      CopyEntryExec e ⟨label,payload⟩ (q+r+8)

theorem copyEntry_exec (e : Entry) :
    CopyEntryExec e (copyEntry e).1 (copyEntry e).2 :=
  .copy _ _ _ _ (copyBits_exec e.label) (copy_exec e.payload)

theorem CopyEntryExec.result {e out : Entry} {q : ℕ} (h : CopyEntryExec e out q) :
    out=(copyEntry e).1 ∧ q=(copyEntry e).2 := by
  cases h with
  | copy label payload q r hl hp =>
      have l := hl.result
      have p := hp.result
      constructor <;> simp only [copyEntry,← l.1,← l.2,← p.1,← p.2]

@[simp] theorem copyEntry_value (e : Entry) : (copyEntry e).1=e := by
  cases e
  simp [copyEntry,(copyBits_spec _).1,(copy_spec _).1]

def copyBound (B S : ℕ) : ℕ := 4*B+4*S+9

theorem copyEntry_bound (e : Entry) (B S : ℕ)
    (hl : e.label.length ≤ B) (hp : e.payload.size ≤ S) :
    (copyEntry e).2 ≤ copyBound B S := by
  have hlabel := (copyBits_spec e.label).2
  have hpay := (copy_spec e.payload).2
  change (copyBits e.label).2+(copy e.payload).2+8 ≤ _
  unfold copyBound
  omega

/-- Outer none is malformed-input failure; some none is an ordinary miss. -/
def scan (mode : Mode) : List Entry → Option (Option Entry) × ℕ
  | [] => (some none,1)
  | e::es =>
      let a := check mode e.label
      match a.1 with
      | none => (none,a.2+8)
      | some true =>
          let c := copyEntry e
          (some (some c.1),a.2+c.2+12)
      | some false =>
          let r := scan mode es
          (r.1,a.2+r.2+8)

inductive ScanExec (mode : Mode) : List Entry → Option (Option Entry) → ℕ → Prop
  | nil : ScanExec mode [] (some none) 1
  | malformed (e : Entry) (es : List Entry) (q : ℕ) :
      CheckExec mode e.label none q → ScanExec mode (e::es) none (q+8)
  | hit (e : Entry) (es : List Entry) (out : Entry) (q r : ℕ) :
      CheckExec mode e.label (some true) q → CopyEntryExec e out r →
      ScanExec mode (e::es) (some (some out)) (q+r+12)
  | next (e : Entry) (es : List Entry) (out : Option (Option Entry)) (q r : ℕ) :
      CheckExec mode e.label (some false) q → ScanExec mode es out r →
      ScanExec mode (e::es) out (q+r+8)

theorem ScanExec.result {mode : Mode} {es : List Entry} {out : Option (Option Entry)} {q : ℕ}
    (h : ScanExec mode es out q) : out=(scan mode es).1 ∧ q=(scan mode es).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | malformed e es q hc =>
      have c := hc.result
      constructor <;> simp only [scan,← c.1,← c.2]
  | hit e es out q r hc hp =>
      have c := hc.result
      have p := hp.result
      constructor <;> simp only [scan,← c.1,← c.2,← p.1,← p.2]
  | next e es out q r hc hr ih =>
      have c := hc.result
      constructor <;> simp only [scan,← c.1,← c.2,← ih.1,← ih.2]

theorem scan_exec (mode : Mode) (es : List Entry) :
    ScanExec mode es (scan mode es).1 (scan mode es).2 := by
  induction es with
  | nil => exact .nil
  | cons e es ih =>
      have hc := check_exec mode e.label
      cases he : (check mode e.label).1 with
      | none =>
          rw [he] at hc
          simpa only [scan,he] using ScanExec.malformed e es _ hc
      | some b =>
          cases b with
          | true =>
              rw [he] at hc
              simpa only [scan,he] using ScanExec.hit e es _ _ _ hc (copyEntry_exec e)
          | false =>
              rw [he] at hc
              simpa only [scan,he] using ScanExec.next e es _ _ _ hc ih

/-- A proof-side first-hit transport. `encode` and P are never executable
arguments of scan; the subsequent two theorems instantiate the fixed modes. -/
theorem scan_refines {α : Type*} (P : α → Prop) [DecidablePred P]
    (sourceTest : CountedSearch.Test P) (encode : α → Entry) (mode : Mode) (xs : List α)
    (hcheck : ∀ x∈xs, (check mode (encode x).label).1=some (decide (P x))) :
    (scan mode (xs.map encode)).1=
      some ((CountedSearch.scan P sourceTest xs).1.map (fun e => encode e.val)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hcheck x (by simp)
      have ht := ih (fun y hy => hcheck y (by simp [hy]))
      cases hs : (sourceTest x).1 with
      | isTrue hp =>
          have hc : (check mode (encode x).label).1=some true := by simpa [hp] using hx
          simp [scan,hc,CountedSearch.scan,hs]
      | isFalse hp =>
          have hc : (check mode (encode x).label).1=some false := by simpa [hp] using hx
          simp [scan,hc,CountedSearch.scan,hs,ht,Option.map_map,Function.comp_def]

/-- Exact concrete equality-lookup instance used by visit and extract. -/
theorem lookup_refines {α : Type*} {m : ℕ} (key : α → Fin m) (encode : α → Entry)
    (xs : List α) (target : Fin m) (tb : Bits) (ht : value tb=target.val)
    (hlabel : ∀ x∈xs, value (encode x).label=(key x).val) :
    (scan (.lookup tb) (xs.map encode)).1 =
      some ((CountedSearch.scan (fun x => key x=target)
        (fun x => (inferInstanceAs (Decidable (key x=target)),1)) xs).1.map
          (fun e => encode e.val)) := by
  apply scan_refines
  intro x hx
  have he : (BinaryArithmetic.compare (encode x).label tb).equal=decide (key x=target) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [hlabel x hx,ht,decide_eq_true_eq,Fin.ext_iff] using
      (BinaryArithmetic.compare_spec (encode x).label tb).2.1
  simp only [check,he]

/-- Exact restricted-adjacency lookup instance used by visit's second scan. -/
theorem restricted_refines {α : Type*} {m : ℕ}
    (D : EncodedShortcutReachability.Input m) (key : α → Fin m) (encode : α → Entry)
    (xs : List α) (s t u : Fin m) (sb tb ub : Bits)
    (hs : value sb=s.val) (ht : value tb=t.val) (hu : value ub=u.val)
    (hlabel : ∀ x∈xs, value (encode x).label=(key x).val) :
    (scan (.restricted sb tb ub (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed)) (xs.map encode)).1 =
      some ((CountedSearch.scan (fun x => (D.restrictedGraph s t).Adj u (key x))
        (fun x => D.restrictedTest s t u (key x)) xs).1.map (fun e => encode e.val)) := by
  apply scan_refines
  intro x hx
  change (EncodedRestrictedTestExec.test sb tb ub (encode x).label
    (EncodedCellAccess.flagTable D.adjacency) (EncodedRestrictedTestExec.maskValue D.removed)).1 =
      some (@decide ((D.restrictedGraph s t).Adj u (key x)) _)
  rw [EncodedRestrictedTestExec.test_get D s t u (key x) sb tb ub (encode x).label
    hs ht hu (hlabel x hx)]
  apply congrArg some
  change D.restrictedBool s t u (key x) = @decide (D.restrictedBool s t u (key x)=true) _
  exact (@Bool.decide_eq_true (D.restrictedBool s t u (key x)) (D.restrictedTest s t u (key x)).1).symm

def scanBound (length C B S : ℕ) : ℕ := length*(C+12)+copyBound B S+1

theorem scan_bound (mode : Mode) (es : List Entry) (C B S : ℕ)
    (hc : ∀ e∈es, (check mode e.label).2 ≤ C)
    (hl : ∀ e∈es, e.label.length ≤ B)
    (hp : ∀ e∈es, e.payload.size ≤ S) :
    (scan mode es).2 ≤ scanBound es.length C B S := by
  induction es with
  | nil => simp [scan,scanBound]
  | cons e es ih =>
      have hce := hc e (by simp)
      have hcopy := copyEntry_bound e B S (hl e (by simp)) (hp e (by simp))
      have hr := ih (fun x hx => hc x (by simp [hx]))
        (fun x hx => hl x (by simp [hx])) (fun x hx => hp x (by simp [hx]))
      simp only [scan,List.length_cons]
      unfold scanBound at *
      split <;> dsimp only <;> nlinarith

theorem lookup_check_bound (label target : Bits) (B : ℕ)
    (hl : label.length ≤ B) (ht : target.length ≤ B) :
    (check (.lookup target) label).2 ≤ 16*(B+1)+4 := by
  have h := (BinaryArithmetic.compare_spec label target).2.2
  have hm := max_le hl ht
  change (BinaryArithmetic.compare label target).steps+4 ≤ _
  omega

theorem restricted_check_bound {m : ℕ} (D : EncodedShortcutReachability.Input m)
    (s t u label : Bits) (B : ℕ)
    (hs : s.length ≤ B) (ht : t.length ≤ B) (hu : u.length ≤ B) (hl : label.length ≤ B) :
    (check (.restricted s t u (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed)) label).2 ≤
      EncodedRestrictedTestExec.testBound m B+4 :=
  Nat.add_le_add_right (EncodedRestrictedTestExec.test_bound D s t u label B hs ht hu hl) 4

/-- The payload is a finite retained value, not an arbitrary path evaluator. -/
def entryValue (e : Entry) : Value := .pair (.word e.label) e.payload

theorem representation_bound (es : List Entry) (B S : ℕ)
    (hl : ∀ e∈es, e.label.length ≤ B) (hp : ∀ e∈es, e.payload.size ≤ S) :
    (sequence (es.map entryValue)).size ≤ es.length*(B+S+3)+1 := by
  have h := sequence_size_bound (xs := es.map entryValue) (S := B+S+2) (by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    have hlabel := hl e he
    have hpay := hp e he
    simp only [entryValue,Value.size]
    omega)
  simpa [Nat.add_assoc] using h


/-- Shortcut decisions instantiate the same routine with a fixed empty payload.
No dependent path or path evaluator is stored in this specialization. -/
def keyEntry (label : Bits) : Entry := ⟨label,.empty⟩

@[simp] theorem keyEntry_payload_size (label : Bits) : (keyEntry label).payload.size=1 := rfl

theorem keyOnly_bound (mode : Mode) (keys : List Bits) (C B : ℕ)
    (hc : ∀ label∈keys, (check mode label).2 ≤ C)
    (hl : ∀ label∈keys, label.length ≤ B) :
    (scan mode (keys.map keyEntry)).2 ≤ scanBound keys.length C B 1 := by
  have h := scan_bound mode (keys.map keyEntry) C B 1
    (by
      intro e he
      obtain ⟨label,hlabel,rfl⟩ := List.mem_map.mp he
      exact hc label hlabel)
    (by
      intro e he
      obtain ⟨label,hlabel,rfl⟩ := List.mem_map.mp he
      exact hl label hlabel)
    (by
      intro e he
      obtain ⟨label,hlabel,rfl⟩ := List.mem_map.mp he
      rfl)
  simpa only [List.length_map] using h

/-- Exact found/miss projection for the caller's root-list refinement. The
whole first-hit entry is still produced by the same concrete scan body. -/
theorem scan_found {α : Type*} (P : α → Prop) [DecidablePred P]
    (encode : α → Entry) (mode : Mode) (xs : List α)
    (hcheck : ∀ x∈xs, (check mode (encode x).label).1=some (decide (P x))) :
    (scan mode (xs.map encode)).1.map Option.isSome = some (xs.any (fun x => decide (P x))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hcheck x (by simp)
      have ht := ih (fun y hy => hcheck y (by simp [hy]))
      by_cases hp : P x
      · have hc : (check mode (encode x).label).1=some true := by simpa [hp] using hx
        simp [scan,hc,hp]
      · have hc : (check mode (encode x).label).1=some false := by simpa [hp] using hx
        simp [scan,hc,hp,ht]

end DirectedFlowCutGap.EncodedSearchScanExec
