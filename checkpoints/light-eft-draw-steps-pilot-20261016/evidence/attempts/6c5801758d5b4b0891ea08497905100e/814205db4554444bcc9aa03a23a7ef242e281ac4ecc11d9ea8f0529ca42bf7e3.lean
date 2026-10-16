import LightEFTSpanners.StoredForestCandidateEncoding

namespace LightEFTSpanners.StoredForestBank
open Controller
structure Input where
  edge : StoredEdges.Edge
  bank : StoredDrawLookup.Bank
  deriving DecidableEq, Repr
inductive State where
  | inputs : List Input → List StoredCandidates.Input → State
  | call : Input → List Input → List StoredCandidates.Input → StoredForestCandidate.State → State
  | reverse : List StoredCandidates.Input → List StoredCandidates.Input → State
  | halt : List StoredCandidates.Input → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (fs : List (List StoredEdges.Edge)) (W : StoredRecords.Weights) (t : ℚ) : State → Option State
  | .inputs [] acc => some (.reverse acc [])
  | .inputs (r::rs) acc => some (.call r rs acc (.inputs (.forests (.forests 0 fs []))))
  | .call _ rs acc (.halt out) => some (.inputs rs (out::acc))
  | .call r rs acc s => (StoredForestCandidate.transition n r.bank r.edge W t s).map (State.call r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def value {n : ℕ} (fs : List (List (Fin n × Fin n))) (W : StoredRecords.Weights) (t : ℚ) (rs : List Input) :
    List StoredCandidates.Input := rs.map fun r => StoredForestCandidate.value fs r.bank r.edge W t

def scanBound (n : ℕ) (fs : List (List StoredEdges.Edge)) (rs : List Input) : ℕ :=
  (rs.map fun r => StoredForestCandidate.bound n fs r.bank r.edge+2).sum+1

theorem call_lift (n : ℕ) (fs : List (List StoredEdges.Edge)) (W : StoredRecords.Weights) (t : ℚ)
    (r : Input) (rs : List Input) (acc : List StoredCandidates.Input) {k : ℕ} {s u : StoredForestCandidate.State}
    (h : Trace (StoredForestCandidate.transition n r.bank r.edge W t) k s u) :
    Trace (transition n fs W t) k (.call r rs acc s) (.call r rs acc u) := by
  induction h with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredForestCandidate.transition] at he
    | inputs st => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call r rs acc)) he
    | candidate st => simpa only [transition,Option.map_some] using congrArg (Option.map (State.call r rs acc)) he

theorem scan_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (W : StoredRecords.Weights) (t : ℚ)
    (rs : List Input) (acc : List StoredCandidates.Input) :
    ∃ k,k ≤ scanBound n (fs.map StoredEdges.encode) rs ∧
      Trace (transition n (fs.map StoredEdges.encode) W t) k (.inputs rs acc)
        (.reverse ((value fs W t rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact ⟨1,by simp [scanBound],Trace.one rfl⟩
  | cons r rs ih =>
    obtain ⟨k,hk,ht⟩ := StoredForestCandidate.full_trace fs r.bank r.edge W t
    have a := Trace.one (show transition n (fs.map StoredEdges.encode) W t (.inputs (r::rs) acc)=
      some (.call r rs acc (.inputs (.forests (.forests 0 (fs.map StoredEdges.encode) [])))) from rfl)
    have b := call_lift n (fs.map StoredEdges.encode) W t r rs acc ht
    have c := Trace.one (show transition n (fs.map StoredEdges.encode) W t
      (.call r rs acc (.halt (StoredForestCandidate.value fs r.bank r.edge W t)))=
      some (.inputs rs ((StoredForestCandidate.value fs r.bank r.edge W t)::acc)) from rfl)
    obtain ⟨l,hl,hu⟩ := ih ((StoredForestCandidate.value fs r.bank r.edge W t)::acc)
    refine ⟨1+k+1+l,?_,?_⟩
    · simp only [scanBound,List.map_cons,List.sum_cons] at *
      omega
    · simpa [value,List.reverse_cons,List.append_assoc,Nat.add_assoc] using a.trans (b.trans (c.trans hu))
end LightEFTSpanners.StoredForestBank
