import DirectedFlowCutGap.EncodedRootSearchExec

/-!
# Numeric diagonal guard for the closed shortcut search

The endpoint labels are compared as stored binary words, including padding.
An equal pair returns false before inspecting the graph representation. Every
other pair runs the fixed root-only search. The result agrees with the actual
shortcut predicate, rather than with unrestricted reflexive reachability.

The cost is the local charge of the named scalar comparison and fixed search
body. Retaining inputs and copying argument frames are separate obligations.
-/
namespace DirectedFlowCutGap.EncodedShortcutExec
open BinaryArithmetic EncodedSequenceAccess EncodedRootVisitExec
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def shortcut (D : Input) (vertices : List Bits) : Option Bool × ℕ :=
  let c := BinaryArithmetic.compare D.source D.target
  if c.equal then (some false,c.steps+4) else
    let r := EncodedRootSearchExec.search D vertices
    (r.1,c.steps+r.2+8)

inductive ShortcutExec (D : Input) (vertices : List Bits) : Option Bool → ℕ → Prop
  | diagonal : (BinaryArithmetic.compare D.source D.target).equal=true →
      ShortcutExec D vertices (some false)
        ((BinaryArithmetic.compare D.source D.target).steps+4)
  | search (out : Option Bool) (q : ℕ) :
      (BinaryArithmetic.compare D.source D.target).equal=false →
      EncodedRootSearchExec.SearchExec D vertices out q →
      ShortcutExec D vertices out ((BinaryArithmetic.compare D.source D.target).steps+q+8)

theorem ShortcutExec.result {D : Input} {vertices : List Bits} {out : Option Bool} {q : ℕ}
    (h : ShortcutExec D vertices out q) :
    out=(shortcut D vertices).1 ∧ q=(shortcut D vertices).2 := by
  cases h with
  | diagonal hc => constructor <;> simp only [shortcut,hc,ite_true]
  | search out q hc hr =>
      have h := hr.result
      constructor <;> simp only [shortcut,hc,Bool.false_eq_true,ite_false,← h.1,← h.2]

theorem shortcut_exec (D : Input) (vertices : List Bits) :
    ShortcutExec D vertices (shortcut D vertices).1 (shortcut D vertices).2 := by
  cases hc : (BinaryArithmetic.compare D.source D.target).equal with
  | true => simpa only [shortcut,hc,ite_true] using ShortcutExec.diagonal (vertices := vertices) hc
  | false =>
      simpa only [shortcut,hc,Bool.false_eq_true,ite_false] using
        ShortcutExec.search _ _ hc (EncodedRootSearchExec.search_exec D vertices)

variable {m : ℕ} (D : EncodedShortcutReachability.Input m)
variable (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val)
include he

theorem compare_labels (s t : Fin m) :
    (BinaryArithmetic.compare (encode s) (encode t)).equal=decide (s=t) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [he,decide_eq_true_eq,Fin.ext_iff] using
    (BinaryArithmetic.compare_spec (encode s) (encode t)).2.1

/-- Exact observation of the original shortcut program with its usual finite
dictionary; the dictionary and encoding occur only in this proof statement. -/
theorem shortcut_refines (E : ResidualSearch.Enumeration (Fin m)) (s t : Fin m) :
    (shortcut (inputValue D (encode s) (encode t)) (E.vertices.map encode)).1 =
      some (D.shortcut E (Fin.fintype m) s t).1 := by
  have hc := compare_labels encode he s t
  have hr := EncodedRootSearchExec.search_found D encode he s t E
  by_cases h : s=t
  · have hct : (BinaryArithmetic.compare (encode s) (encode t)).equal=true :=
      hc.trans (decide_eq_true_eq.mpr h)
    simp only [shortcut,inputValue,hct,ite_true,
      EncodedShortcutReachability.Input.shortcut,ite_eq_left h]
  · simp only [shortcut,inputValue,hc,decide_eq_false_iff_not.mpr h,
      Bool.false_eq_true,ite_false,EncodedShortcutReachability.Input.shortcut,
      ite_eq_right h]
    exact hr

theorem shortcut_survivors (E : ResidualSearch.Enumeration (Fin m))
    (s t : ShortcutContraction.Survivor D.removedSet) :
    (shortcut (inputValue D (encode s.val) (encode t.val)) (E.vertices.map encode)).1 =
        some true ↔ (ShortcutContraction.graph D.graph D.removedSet).Adj s t := by
  rw [shortcut_refines D encode he E]
  simpa only [Option.some.injEq] using (D.shortcut_refines E (Fin.fintype m) s t)

def shortcutBound (m B : ℕ) : ℕ := EncodedRootSearchExec.searchBound m B+16*(B+1)+8

theorem shortcut_bound (E : ResidualSearch.Enumeration (Fin m)) (s t : Fin m) (B : ℕ)
    (hw : ∀ v, (encode v).length ≤ B) :
    (shortcut (inputValue D (encode s) (encode t)) (E.vertices.map encode)).2 ≤
      shortcutBound m B := by
  have hc := (BinaryArithmetic.compare_spec (encode s) (encode t)).2.2
  have hm := max_le (hw s) (hw t)
  have hr := EncodedRootSearchExec.search_bound D encode he s t E B hw
  simp only [inputValue] at hr
  cases hcEq : (BinaryArithmetic.compare (encode s) (encode t)).equal with
  | false =>
      simp only [shortcut,shortcutBound,inputValue,hcEq,Bool.false_eq_true,ite_false]
      omega
  | true =>
      simp only [shortcut,shortcutBound,inputValue,hcEq,ite_true]
      omega

end DirectedFlowCutGap.EncodedShortcutExec
