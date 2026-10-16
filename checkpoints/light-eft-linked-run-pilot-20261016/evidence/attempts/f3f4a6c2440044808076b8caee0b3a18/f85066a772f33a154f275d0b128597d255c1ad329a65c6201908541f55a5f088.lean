import LightEFTSpanners.StoredForestBankExecutable
import LightEFTSpanners.StoredCandidateExecutable

namespace LightEFTSpanners.StoredForestCandidates
open Controller
inductive State where
  | prepare : StoredForestBank.State → State
  | select : StoredCandidates.State → State
  deriving DecidableEq, Repr

def transition (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) : State → Option State
  | .prepare (.halt rs) => some (.select (.candidates rs E))
  | .prepare s => (StoredForestBank.transition n fs W t s).map State.prepare
  | .select s => (StoredCandidates.transition Q W n h s).map State.select

theorem prepare_lift (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) {k : ℕ} {s u : StoredForestBank.State}
    (ht : Trace (StoredForestBank.transition n fs W t) k s u) :
    Trace (transition fs Q E W n h t) k (.prepare s) (.prepare u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredForestBank.transition] at he
    | inputs _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | call _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he

theorem select_lift (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) {k : ℕ} {s u : StoredCandidates.State}
    (ht : Trace (StoredCandidates.transition Q W n h) k s u) :
    Trace (transition fs Q E W n h t) k (.select s) (.select u) := by
  induction ht with
  | refl => exact .refl _
  | cons he _ ih =>
    exact Trace.cons (by simpa only [transition,Option.map_some] using congrArg (Option.map State.select) he) ih

theorem prepared_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (StoredForestBank.TypedInput n)) :
    ∃ k, k ≤ StoredForestBank.bound n (fs.map StoredEdges.encode) (rs.map StoredForestBank.encode)+1+
      StoredCandidates.work Q w h (StoredForestBank.typedValue fs w t rs) E ∧
      Trace (transition (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredRecords.encodeWeights w) n h t) k
        (.prepare (.inputs (rs.map StoredForestBank.encode) []))
        (.select (.halt (StoredEdges.encode (StoredCandidates.selected Q w h
          (StoredForestBank.typedValue fs w t rs) E)))) := by
  obtain ⟨k,hk,ht⟩ := StoredForestBank.full_trace fs (StoredRecords.encodeWeights w) t (rs.map StoredForestBank.encode)
  have a := prepare_lift (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n h t ht
  have he : StoredForestBank.value fs (StoredRecords.encodeWeights w) t (rs.map StoredForestBank.encode)=
      (StoredForestBank.typedValue fs w t rs).map StoredCandidates.encode := by
    rw [←StoredForestBank.execute_eq,StoredForestBank.execute_encoded]
  rw [he] at a
  have b := Trace.one (show transition (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n h t
    (.prepare (.halt ((StoredForestBank.typedValue fs w t rs).map StoredCandidates.encode)))=
    some (.select (.candidates ((StoredForestBank.typedValue fs w t rs).map StoredCandidates.encode)
      (StoredEdges.encode E))) from rfl)
  obtain ⟨l,hl,hu⟩ := StoredCandidates.candidates_trace Q E w h (StoredForestBank.typedValue fs w t rs)
  have c := select_lift (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n h t hu
  exact ⟨_,by omega,a.trans (b.trans c)⟩
end LightEFTSpanners.StoredForestCandidates
