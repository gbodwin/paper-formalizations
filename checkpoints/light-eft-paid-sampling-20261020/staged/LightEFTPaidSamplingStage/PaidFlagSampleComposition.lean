import LightEFTPaidSamplingStage.PaidFlagSerialization
import LightEFTSpanners.StoredFlagSampleExecutable

/-!
Literal sequential composition of response serialization with the existing
stored-edge flag filter. The handoff is one constructor-only transition; no
arbitrary initializer, uncharged encoding callback or padded output cost is used.
Keys are supplied raw edge pairs. Enumeration, bias generation and bit costs
remain outside this component.
-/
namespace LightEFTSpanners.PaidFlagSampleComposition
open Controller

inductive State where
  | serialize : PaidFlagSerialization.State StoredEdges.Edge → State
  | filter : StoredFlagSample.State → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .serialize (.halt rows) => some (.filter (.scan rows []))
  | .serialize s => (PaidFlagSerialization.transition s).map .serialize
  | .filter s => (StoredFlagSample.transition s).map .filter

theorem serialize_lift {k : ℕ} {s t : PaidFlagSerialization.State StoredEdges.Edge}
    (h : Trace PaidFlagSerialization.transition k s t) :
    Trace transition k (.serialize s) (.serialize t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u hs _ ih =>
    apply Trace.cons (t := .serialize t) ?_ ih
    cases s <;> simp_all [transition, PaidFlagSerialization.transition]

theorem filter_lift {k : ℕ} {s t : StoredFlagSample.State}
    (h : Trace StoredFlagSample.transition k s t) :
    Trace transition k (.filter s) (.filter t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u hs _ ih =>
    apply Trace.cons (t := .filter t) ?_ ih
    simp [transition, hs]

/-- Response consumption, raw-record construction and the actual stored filter
have one composed operational trace. The response list is occurrence-indexed;
neither duplicate keys nor false responses are removed before serialization. -/
theorem full_trace (keys : List StoredEdges.Edge) (bits : List Bool)
    (hlen : bits.length = keys.length) :
    ∃ k, k ≤ 5*keys.length+5 ∧
      Trace transition k (.serialize (.collect keys bits []))
        (.filter (.halt (StoredFlagSample.value (keys.zip bits)))) := by
  have hs := serialize_lift (PaidFlagSerialization.full_trace keys bits hlen)
  have hh := Trace.one (show transition (.serialize (.halt (keys.zip bits))) =
    some (.filter (.scan (keys.zip bits) [])) from rfl)
  obtain ⟨k,hk,hf⟩ := StoredFlagSample.full_trace (keys.zip bits)
  have hz := PaidFlagSerialization.response_count keys bits hlen
  refine ⟨(3*keys.length+2)+1+k, ?_, (hs.trans hh).trans (filter_lift hf)⟩
  unfold StoredFlagSample.bound at hk
  rw [hz] at hk
  omega

def execute (keys : List StoredEdges.Edge) (bits : List Bool) : Option (List StoredEdges.Edge) :=
  match Controller.run transition (5*keys.length+5) (.serialize (.collect keys bits [])) with
  | .filter (.halt rows) => some rows
  | _ => none

theorem execute_eq (keys : List StoredEdges.Edge) (bits : List Bool)
    (hlen : bits.length = keys.length) :
    execute keys bits = some (StoredFlagSample.value (keys.zip bits)) := by
  obtain ⟨k,hk,ht⟩ := full_trace keys bits hlen
  have he : 5*keys.length+5 = k+(5*keys.length+5-k) := by omega
  unfold execute
  rw [he, Controller.run_add, ht.run_eq, Controller.run_terminal _ _ rfl]

end LightEFTSpanners.PaidFlagSampleComposition
