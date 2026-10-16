import LightEFTSpanners.StoredCandidateMachine

namespace LightEFTSpanners.StoredCandidates
open Controller
structure TypedInput (n : ℕ) where
  edge : Fin n × Fin n
  budget : ℚ
  hosts : List (StoredHosts.TypedInput n)

def encode {n : ℕ} (R : TypedInput n) : Input :=
  ⟨(R.edge.1.val,R.edge.2.val),R.budget,R.hosts.map StoredHosts.encode⟩

def accept {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) (R : TypedInput n) : Bool :=
  decide (h≤StoredHosts.votes Q E w R.edge.1 R.edge.2 R.budget R.hosts)

def updated {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) (R : TypedInput n) : List (Fin n × Fin n) :=
  if accept Q E w h R then R.edge::E else E

def selected {n : ℕ} (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) : List (TypedInput n) → List (Fin n × Fin n) → List (Fin n × Fin n)
  | [],E => E
  | R::rs,E => selected Q w h rs (updated Q E w h R)

def work {n : ℕ} (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) : List (TypedInput n) → List (Fin n × Fin n) → ℕ
  | [],_ => 1
  | R::rs,E => (R.hosts.map fun H => StoredHosts.hostBound Q E H+2).sum+3+
      work Q w h rs (updated Q E w h R)

theorem candidate_trace {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (R : TypedInput n) (rs : List Input) :
    ∃ k,k≤(R.hosts.map fun H => StoredHosts.hostBound Q E H+2).sum+3 ∧
      Trace (transition (StoredEdges.encode Q) (StoredRecords.encodeWeights w) n h) k
        (.candidates (encode R::rs) (StoredEdges.encode E))
        (.candidates rs (StoredEdges.encode (updated Q E w h R))) := by
  obtain ⟨k,hk,ht⟩ := StoredHosts.hosts_trace Q E w R.edge.1 R.edge.2 h R.budget R.hosts 0
  simp only [zero_add] at ht
  have h0 := Trace.one (show transition (StoredEdges.encode Q) (StoredRecords.encodeWeights w) n h
    (.candidates (encode R::rs) (StoredEdges.encode E))=
    some (.call (encode R) rs (StoredEdges.encode E) (.hosts (encode R).hosts 0)) from rfl)
  have h1 := call_lift (StoredEdges.encode Q) (StoredRecords.encodeWeights w) n h
    (encode R) rs (StoredEdges.encode E) ht
  have h2 := Trace.one (show transition (StoredEdges.encode Q) (StoredRecords.encodeWeights w) n h
    (.call (encode R) rs (StoredEdges.encode E) (.halt (accept Q E w h R)))=
    some (.candidates rs (StoredEdges.encode (updated Q E w h R))) from by
      cases hb : accept Q E w h R <;> simp [transition,updated,hb,StoredEdges.encode,encode])
  exact ⟨1+k+1,by omega,h0.trans (h1.trans h2)⟩

theorem candidates_trace {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (rs : List (TypedInput n)) :
    ∃ k,k≤work Q w h rs E ∧
      Trace (transition (StoredEdges.encode Q) (StoredRecords.encodeWeights w) n h) k
        (.candidates (rs.map encode) (StoredEdges.encode E))
        (.halt (StoredEdges.encode (selected Q w h rs E))) := by
  induction rs generalizing E with
  | nil => exact ⟨1,Nat.le_refl 1,Trace.one rfl⟩
  | cons R rs ih =>
    obtain ⟨k,hk,ht⟩ := candidate_trace Q E w h R (rs.map encode)
    obtain ⟨l,hl,hs⟩ := ih (updated Q E w h R)
    exact ⟨k+l,by simp only [work];omega,ht.trans hs⟩
end LightEFTSpanners.StoredCandidates
