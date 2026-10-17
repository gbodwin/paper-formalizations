import LightEFTSpanners.StoredPreparedHostRecords

namespace LightEFTSpanners.StoredPreparedHostVote
open Controller
open StoredHostPreparation (Record TypedRecord)
inductive State where
  | prepare : StoredPreparedHostRecords.State → State
  | vote : StoredHosts.State → State
  | halt : Bool → State
  deriving DecidableEq, Repr

def transition (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) : State → Option State
  | .prepare (.halt rs) => some (.vote (.hosts rs 0))
  | .prepare s => (StoredPreparedHostRecords.transition (u,v) s).map State.prepare
  | .vote (.halt yes) => some (.halt yes)
  | .vote s => (StoredHosts.transition Q E W n u v h budget s).map State.vote
  | .halt _ => none

theorem prepare_lift (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) {k : ℕ} {s t : StoredPreparedHostRecords.State}
    (ht : Trace (StoredPreparedHostRecords.transition (u,v)) k s t) :
    Trace (transition Q E W n u v h budget) k (.prepare s) (.prepare t) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredPreparedHostRecords.transition] at he
    | prepare _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | copy _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.prepare) he

theorem vote_lift (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) {k : ℕ} {s t : StoredHosts.State}
    (ht : Trace (StoredHosts.transition Q E W n u v h budget) k s t) :
    Trace (transition Q E W n u v h budget) k (.vote s) (.vote t) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s t z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredHosts.transition] at he
    | hosts _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.vote) he
    | call _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map State.vote) he

def inputBound (n : ℕ) (Q E : List StoredEdges.Edge) (rs : List Record) : ℕ :=
  StoredPreparedHostRecords.inputBound rs+
    StoredHosts.bound (StoredHosts.inputBound n Q E) (rs.map Record.host)+2

theorem filter_sum_le {α : Type*} (p : α → Bool) (f : α → ℕ) (xs : List α) :
    ((xs.filter p).map f).sum≤(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp] <;> omega

theorem prepared_vote_trace {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (h : ℕ) (budget : ℚ)
    (rs : List (TypedRecord n)) :
    ∃ k,k ≤ inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map StoredHostPreparation.encode) ∧
      Trace (transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
        n u.val v.val h budget) k
        (.prepare (.prepare (.records (rs.map StoredHostPreparation.encode) [])))
        (.halt (decide (h≤StoredHosts.votes Q E w u v budget
          ((rs.filter (StoredHostPreparation.eligible u v)).map TypedRecord.host)))) := by
  let raw := rs.map StoredHostPreparation.encode
  let chosen := (rs.filter (StoredHostPreparation.eligible u v)).map TypedRecord.host
  have a := prepare_lift (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
    n u.val v.val h budget (StoredPreparedHostRecords.records_trace (u.val,v.val) raw)
  have eq : StoredPreparedHostRecords.result (u.val,v.val) raw=chosen.map StoredHosts.encode := by
    rw [←StoredPreparedHostRecords.execute_eq,StoredPreparedHostRecords.execute_encoded]
    simp [chosen,List.map_map,Function.comp_def]
  rw [eq] at a
  obtain ⟨k,hk,ht⟩ := StoredHosts.hosts_trace Q E w u v h budget chosen 0
  simp only [Nat.zero_add] at ht
  have vote := vote_lift (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
    n u.val v.val h budget ht
  have handover := Trace.one (show transition (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n u.val v.val h budget (.prepare (.halt (chosen.map StoredHosts.encode)))=
      some (.vote (.hosts (chosen.map StoredHosts.encode) 0)) from rfl)
  have finish := Trace.one (show transition (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n u.val v.val h budget
      (.vote (.halt (decide (h≤StoredHosts.votes Q E w u v budget chosen))))=
        some (.halt (decide (h≤StoredHosts.votes Q E w u v budget chosen))) from rfl)
  refine ⟨_,?_,a.trans (handover.trans (vote.trans finish))⟩
  have prep := StoredPreparedHostRecords.steps_le_input (u.val,v.val) raw
  have all := filter_sum_le (StoredHostPreparation.eligible u v)
    (fun r : TypedRecord n => StoredHosts.hostBound Q E r.host+2) rs
  simp only [chosen,List.map_map,Function.comp_def] at hk
  have hb : k≤StoredHosts.bound (StoredHosts.inputBound n (StoredEdges.encode Q) (StoredEdges.encode E))
      (raw.map Record.host) := by
    unfold StoredHosts.bound
    simp only [raw,List.map_map,Function.comp_def,StoredHostPreparation.encode,
      StoredHosts.inputBound,StoredHosts.hostBound,StoredHosts.encode] at *
    omega
  unfold inputBound
  dsimp only [raw] at prep hb ⊢
  omega
end LightEFTSpanners.StoredPreparedHostVote
