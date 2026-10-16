import LightEFTSpanners.StoredForestDrawAttachmentBound

namespace LightEFTSpanners.StoredForestInput
open Controller
inductive State where
  | forests : StoredForestHosts.State → State
  | attach : StoredForestDrawAttachment.State → State
  | halt : List StoredComponentRecord.Input → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (bank : StoredDrawLookup.Bank) : State → Option State
  | .forests (.halt rs) => some (.attach (.records rs []))
  | .forests s => (StoredForestHosts.transition n s).map State.forests
  | .attach (.halt rs) => some (.halt rs)
  | .attach s => (StoredForestDrawAttachment.transition n bank s).map State.attach
  | .halt _ => none

def value {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank) : List StoredComponentRecord.Input :=
  StoredForestDrawAttachment.value n bank (StoredForestHosts.value 0 fs)

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank) : ℕ :=
  StoredForestHosts.bound n fs+StoredForestDrawAttachment.bound bank (fs.length*n)+2

def execute (n : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank) : List StoredComponentRecord.Input :=
  match Controller.run (transition n bank) (bound n fs bank) (.forests (.forests 0 fs [])) with
  | .halt rs => rs
  | _ => []

theorem forests_lift (n : ℕ) (bank : StoredDrawLookup.Bank) {k : ℕ} {s t : StoredForestHosts.State}
    (h : Trace (StoredForestHosts.transition n) k s t) :
    Trace (transition n bank) k (.forests s) (.forests t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredForestHosts.transition] at he
    | forests a b c => simpa only [transition,Option.map_some] using congrArg (Option.map State.forests) he
    | discover a b c d e => simpa only [transition,Option.map_some] using congrArg (Option.map State.forests) he
    | append a b c d => simpa only [transition,Option.map_some] using congrArg (Option.map State.forests) he
    | reverse a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.forests) he

theorem attach_lift (n : ℕ) (bank : StoredDrawLookup.Bank) {k : ℕ} {s t : StoredForestDrawAttachment.State}
    (h : Trace (StoredForestDrawAttachment.transition n bank) k s t) :
    Trace (transition n bank) k (.attach s) (.attach t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredForestDrawAttachment.transition] at he
    | records a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.attach) he
    | lookup a b c d => simpa only [transition,Option.map_some] using congrArg (Option.map State.attach) he
    | reverse a b => simpa only [transition,Option.map_some] using congrArg (Option.map State.attach) he
end LightEFTSpanners.StoredForestInput
