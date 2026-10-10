import DirectedFlowCutGap.EncodedRestrictedTestExec
import DirectedFlowCutGap.RetainedSurvivorEnumeration

/-!
# Closed retained-mask filtering with binary labels

The scan follows the tail-first order of RetainedSurvivorEnumeration.scan.
Each reached mask lookup is the actual certified sequence read; each kept
binary label is copied bit by bit. Numeric label decoding is used only in the
refinement theorem. The procedure also defines honest failure when it reaches
a malformed retained mask or an out-of-range label; it does not validate unused
mask cells, and the empty input succeeds without a read.

This is a source-bound leaf certificate. Construction of the initial label
list and mask, movement of retained frames, and the enclosing graph builder
remain separate representation and composition obligations. The local work
counter is not a claim about evaluating arbitrary Lean code or its counters.
-/
namespace DirectedFlowCutGap.EncodedSurvivorExec
open BinaryArithmetic EncodedSequenceAccess EncodedRestrictedTestExec

def scan (mask : Value) : List Bits → Option (List Bits) × ℕ
  | [] => (some [],1)
  | b::bs =>
      let t := scan mask bs
      match t.1 with
      | none => (none,t.2+4)
      | some rest =>
          let h := flagAt b mask
          match h.1 with
          | none => (none,t.2+h.2+8)
          | some true => (some rest,t.2+h.2+8)
          | some false =>
              let c := copyBits b
              (some (c.1::rest),t.2+h.2+c.2+12)

inductive ScanExec (mask : Value) : List Bits → Option (List Bits) → ℕ → Prop
  | nil : ScanExec mask [] (some []) 1
  | missingTail (b : Bits) (bs : List Bits) (q : ℕ) :
      ScanExec mask bs none q → ScanExec mask (b::bs) none (q+4)
  | missingHead (b : Bits) (bs rest : List Bits) (q r : ℕ) :
      ScanExec mask bs (some rest) q → FlagAtExec b mask none r →
      ScanExec mask (b::bs) none (q+r+8)
  | removed (b : Bits) (bs rest : List Bits) (q r : ℕ) :
      ScanExec mask bs (some rest) q → FlagAtExec b mask (some true) r →
      ScanExec mask (b::bs) (some rest) (q+r+8)
  | kept (b c : Bits) (bs rest : List Bits) (q r k : ℕ) :
      ScanExec mask bs (some rest) q → FlagAtExec b mask (some false) r →
      BitsCopyExec b c k → ScanExec mask (b::bs) (some (c::rest)) (q+r+k+12)

theorem ScanExec.result {mask : Value} {bs : List Bits} {out : Option (List Bits)}
    {q : ℕ} (h : ScanExec mask bs out q) :
    out=(scan mask bs).1 ∧ q=(scan mask bs).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | missingTail b bs q ht ih =>
      constructor <;> simp only [scan,← ih.1,← ih.2]
  | missingHead b bs rest q r ht hh ih =>
      have hr := hh.result
      constructor <;> simp only [scan,← ih.1,← ih.2,← hr.1,← hr.2]
  | removed b bs rest q r ht hh ih =>
      have hr := hh.result
      constructor <;> simp only [scan,← ih.1,← ih.2,← hr.1,← hr.2]
  | kept b c bs rest q r k ht hh hc ih =>
      have hr := hh.result
      have hk := hc.result
      constructor <;> simp only [scan,← ih.1,← ih.2,← hr.1,← hr.2,← hk.1,← hk.2]

theorem scan_exec (mask : Value) (bs : List Bits) :
    ScanExec mask bs (scan mask bs).1 (scan mask bs).2 := by
  induction bs with
  | nil => exact .nil
  | cons b bs ih =>
      cases ht : (scan mask bs).1 with
      | none =>
          rw [ht] at ih
          simpa only [scan,ht] using ScanExec.missingTail b bs _ ih
      | some rest =>
          rw [ht] at ih
          have hh := flagAt_exec b mask
          cases hr : (flagAt b mask).1 with
          | none =>
              rw [hr] at hh
              simpa only [scan,ht,hr] using ScanExec.missingHead b bs rest _ _ ih hh
          | some v =>
              cases v with
              | true =>
                  rw [hr] at hh
                  simpa only [scan,ht,hr] using ScanExec.removed b bs rest _ _ ih hh
              | false =>
                  rw [hr] at hh
                  simpa only [scan,ht,hr] using
                    ScanExec.kept b _ bs rest _ _ _ ih hh (copyBits_exec b)

/-- Padded representations are preserved literally; only their numeric
interpretation determines the mask lookup. -/
theorem scan_refines {m : ℕ} (mask : Vector Bool m) (encode : Fin m → Bits)
    (he : ∀ i, value (encode i)=i.val) (vs : List (Fin m)) :
    (scan (maskValue mask) (vs.map encode)).1 =
      some ((RetainedSurvivorEnumeration.scan mask vs).1.map (fun v => encode v.val)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      have hr := flagAt_get mask v (encode v) (he v)
      cases hv : mask[v.val] <;>
        simp [scan,ih,hr,hv,RetainedSurvivorEnumeration.scan,copyBits_spec]

def stepBound (m B : ℕ) : ℕ := 20*(m+1)*(B+1)+4*B+25

/-- The bound includes tail calls even when a later malformed lookup causes
failure. It uses stored label lengths, never merely their numeric values. -/
theorem scan_bound {m : ℕ} (mask : Vector Bool m) (bs : List Bits) (B : ℕ)
    (hb : ∀ b∈bs, b.length ≤ B) :
    (scan (maskValue mask) bs).2 ≤ bs.length*stepBound m B+1 := by
  induction bs with
  | nil => simp [scan]
  | cons b bs ih =>
      have hh := hb b (by simp)
      have ht := ih (fun x hx => hb x (by simp [hx]))
      have hr := flagAt_bound mask b B hh
      have hc := (copyBits_spec b).2
      simp only [scan,List.length_cons]
      split <;> (try dsimp only)
      · unfold stepBound at *
        nlinarith
      · split <;> (try dsimp only) <;> unfold stepBound at * <;> nlinarith

/-- Every returned word was already present with the same padding. -/
theorem scan_shape (mask : Value) (bs : List Bits) (out : List Bits)
    (ho : (scan mask bs).1=some out) :
    out.length ≤ bs.length ∧ ∀ b∈out, b∈bs := by
  induction bs generalizing out with
  | nil =>
      simp only [scan,Option.some.injEq] at ho
      subst out
      simp
  | cons b bs ih =>
      cases ht : (scan mask bs).1 with
      | none =>
          have hbad : (none : Option (List Bits))=some out := by
            simpa only [scan,ht] using ho
          cases hbad
      | some rest =>
          have hi := ih rest ht
          cases hr : (flagAt b mask).1 with
          | none =>
              have hbad : (none : Option (List Bits))=some out := by
                simpa only [scan,ht,hr] using ho
              cases hbad
          | some v =>
              cases v with
              | true =>
                  simp only [scan,ht,hr,Option.some.injEq] at ho
                  subst out
                  refine ⟨by simpa only [List.length_cons] using hi.1.trans (Nat.le_succ _),?_⟩
                  intro x hx
                  exact List.mem_cons_of_mem b (hi.2 x hx)
              | false =>
                  simp only [scan,ht,hr,(copyBits_spec b).1,Option.some.injEq] at ho
                  subst out
                  refine ⟨by simpa only [List.length_cons] using Nat.succ_le_succ hi.1,?_⟩
                  intro x hx
                  rcases List.mem_cons.mp hx with h|h
                  · exact List.mem_cons.mpr (Or.inl h)
                  · exact List.mem_cons_of_mem b (hi.2 x h)

/-- An explicit bound on the entire returned finite representation. -/
theorem scan_output_size (mask : Value) (bs out : List Bits) (B : ℕ)
    (hb : ∀ b∈bs, b.length ≤ B) (ho : (scan mask bs).1=some out) :
    (sequence (out.map Value.word)).size ≤ bs.length*(B+2)+1 := by
  have hs := scan_shape mask bs out ho
  have hh : ∀ x∈out.map Value.word, x.size ≤ B+1 := by
    intro x hx
    obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hx
    exact Nat.add_le_add_right (hb b (hs.2 b hb')) 1
  have h := sequence_size_bound hh
  simp only [List.length_map,Nat.add_assoc] at h
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (B+2) hs.1) 1)

end DirectedFlowCutGap.EncodedSurvivorExec
