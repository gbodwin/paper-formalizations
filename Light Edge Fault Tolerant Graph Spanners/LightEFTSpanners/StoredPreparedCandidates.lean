import LightEFTSpanners.StoredCandidateBankEncoding
import LightEFTSpanners.StoredCandidateExecutable

namespace LightEFTSpanners.StoredPreparedCandidates
open Controller
inductive State where
  | prepare : StoredCandidateBankPreparation.State → State
  | select : StoredCandidates.State → State
  deriving DecidableEq, Repr

def transition (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) : State → Option State
  | .prepare (.halt rs) => some (.select (.candidates rs E))
  | .prepare s => (StoredCandidateBankPreparation.transition W t s).map State.prepare
  | .select s => (StoredCandidates.transition Q W n h s).map State.select

theorem prepare_lift (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) {k : ℕ} {s u : StoredCandidateBankPreparation.State}
    (ht : Trace (StoredCandidateBankPreparation.transition W t) k s u) :
    Trace (transition Q E W n h t) k (.prepare s) (.prepare u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredCandidateBankPreparation.transition] at he
    | inputs _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | call _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he

theorem select_lift (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) {k : ℕ} {s u : StoredCandidates.State}
    (ht : Trace (StoredCandidates.transition Q W n h) k s u) :
    Trace (transition Q E W n h t) k (.select s) (.select u) := by
  induction ht with
  | refl => exact .refl _
  | cons he _ ih =>
    exact Trace.cons (by simpa only [transition,Option.map_some] using congrArg (Option.map State.select) he) ih

theorem prepared_trace {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ)
    (rs : List (StoredCandidatePreparation.TypedInput n)) :
    ∃ k,k≤StoredCandidateBankPreparation.inputBound (rs.map StoredCandidatePreparation.encode)+1+
      StoredCandidates.work Q w h (rs.map (StoredCandidatePreparation.typedResult w t)) E ∧
      Trace (transition (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredRecords.encodeWeights w) n h t) k
        (.prepare (.inputs (rs.map StoredCandidatePreparation.encode) []))
        (.select (.halt (StoredEdges.encode (StoredCandidates.selected Q w h
          (rs.map (StoredCandidatePreparation.typedResult w t)) E)))) := by
  have a := prepare_lift (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n h t
    (StoredCandidateBankPreparation.bank_trace (StoredRecords.encodeWeights w) t
      (rs.map StoredCandidatePreparation.encode))
  rw [StoredCandidateBankPreparation.result_encoded] at a
  have b := Trace.one (show transition (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n h t
    (.prepare (.halt ((rs.map (StoredCandidatePreparation.typedResult w t)).map StoredCandidates.encode)))=
    some (.select (.candidates ((rs.map (StoredCandidatePreparation.typedResult w t)).map StoredCandidates.encode)
      (StoredEdges.encode E))) from rfl)
  obtain ⟨k,hk,ht⟩ := StoredCandidates.candidates_trace Q E w h
    (rs.map (StoredCandidatePreparation.typedResult w t))
  have c := select_lift (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n h t ht
  have hb := StoredCandidateBankPreparation.steps_le_input (StoredRecords.encodeWeights w)
    (rs.map StoredCandidatePreparation.encode)
  exact ⟨_,by omega,a.trans (b.trans c)⟩
end LightEFTSpanners.StoredPreparedCandidates
