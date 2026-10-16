import LightEFTSpanners.StoredHostMachine

namespace LightEFTSpanners.StoredHosts
open Controller
structure TypedInput (n : ℕ) where
  edges : List (Fin n × Fin n)
  draws : List (List (Fin n × Fin n))

def encode {n : ℕ} (R : TypedInput n) : Input :=
  ⟨StoredEdges.encode R.edges,StoredVote.encodeDraws R.draws⟩

def decision {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (R : TypedInput n) : Bool :=
  SampleVote.finish (SampleVote.failures (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
    (StoredSample.edgeSet R.edges) w u v budget (R.draws.map StoredSample.edgeSet)) R.draws.length

def votes {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (rs : List (TypedInput n)) : ℕ :=
  (rs.map fun R => if decision Q E w u v budget R then 1 else 0).sum

def hostBound {n : ℕ} (Q E : List (Fin n × Fin n)) (R : TypedInput n) : ℕ :=
  StoredVote.bound n (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredEdges.encode R.edges) (StoredVote.encodeDraws R.draws)

theorem host_trace {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (h : ℕ) (budget : ℚ) (R : TypedInput n) (rs : List Input) (count : ℕ) :
    ∃ k,k≤hostBound Q E R+2 ∧ Trace
      (transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
        n u.val v.val h budget) k
      (.hosts (encode R::rs) count)
      (.hosts rs (count+(if decision Q E w u v budget R then 1 else 0))) := by
  obtain ⟨k,hk,ht⟩ := StoredVote.encoded_vote_trace Q E R.edges w u v budget R.draws
  have hb := StoredVote.encoded_bound Q E R.edges w R.draws
  have h0 := Trace.one (show transition (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n u.val v.val h budget (.hosts (encode R::rs) count)=
    some (.call (encode R) rs count (.draws (encode R).draws [])) from rfl)
  have h1 := call_lift (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
    n u.val v.val h budget (encode R) rs count ht
  have h2 := Trace.one (show transition (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredRecords.encodeWeights w) n u.val v.val h budget
    (.call (encode R) rs count (.halt (decision Q E w u v budget R)))=
    some (.hosts rs (count+(if decision Q E w u v budget R then 1 else 0))) from rfl)
  refine ⟨1+k+1,?_,h0.trans (h1.trans h2)⟩
  unfold hostBound
  omega

theorem hosts_trace {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (h : ℕ) (budget : ℚ) (rs : List (TypedInput n)) (count : ℕ) :
    ∃ k,k≤(rs.map fun R => hostBound Q E R+2).sum+1 ∧ Trace
      (transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
        n u.val v.val h budget) k (.hosts (rs.map encode) count)
      (.halt (decide (h≤count+votes Q E w u v budget rs))) := by
  induction rs generalizing count with
  | nil => exact ⟨1,by simp,Trace.one (by simp [transition,votes])⟩
  | cons R rs ih =>
    obtain ⟨k,hk,ht⟩ := host_trace Q E w u v h budget R (rs.map encode) count
    obtain ⟨l,hl,hs⟩ := ih (count+(if decision Q E w u v budget R then 1 else 0))
    refine ⟨k+l,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons];omega
    · simpa only [List.map_cons,votes,List.sum_cons,Nat.add_assoc] using ht.trans hs
end LightEFTSpanners.StoredHosts
