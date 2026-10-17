import LightEFTSpanners.StoredForestBank

namespace LightEFTSpanners.StoredForestBank
open Controller

theorem reverse_trace (n : ℕ) (fs : List (List StoredEdges.Edge)) (W : StoredRecords.Weights) (t : ℚ)
    (rs out : List StoredCandidates.Input) :
    Trace (transition n fs W t) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n fs W t (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (rs : List Input) : ℕ := scanBound n fs rs+rs.length+1

def execute (n : ℕ) (fs : List (List StoredEdges.Edge)) (W : StoredRecords.Weights) (t : ℚ)
    (rs : List Input) : List StoredCandidates.Input :=
  match Controller.run (transition n fs W t) (bound n fs rs) (.inputs rs []) with
  | .halt out => out
  | _ => []

theorem full_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (W : StoredRecords.Weights) (t : ℚ)
    (rs : List Input) : ∃ k,k≤bound n (fs.map StoredEdges.encode) rs ∧
      Trace (transition n (fs.map StoredEdges.encode) W t) k (.inputs rs []) (.halt (value fs W t rs)) := by
  obtain ⟨k,hk,ht⟩ := scan_trace fs W t rs []
  simp only [List.append_nil] at ht
  have hu := reverse_trace n (fs.map StoredEdges.encode) W t (value fs W t rs).reverse []
  refine ⟨k+(rs.length+1),by unfold bound;omega,?_⟩
  simpa [value] using ht.trans hu

theorem execute_eq {n : ℕ} (fs : List (List (Fin n × Fin n))) (W : StoredRecords.Weights) (t : ℚ)
    (rs : List Input) : execute n (fs.map StoredEdges.encode) W t rs=value fs W t rs := by
  obtain ⟨k,hk,ht⟩ := full_trace fs W t rs
  have he : bound n (fs.map StoredEdges.encode) rs=k+(bound n (fs.map StoredEdges.encode) rs-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

structure TypedInput (n : ℕ) where
  edge : Fin n × Fin n
  bank : StoredDrawLookup.TypedBank n

def encode {n : ℕ} (r : TypedInput n) : Input := ⟨(r.edge.1.val,r.edge.2.val),StoredDrawLookup.encode r.bank⟩
def typedValue {n : ℕ} (fs : List (List (Fin n × Fin n))) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (rs : List (TypedInput n)) : List (StoredCandidates.TypedInput n) :=
  rs.map fun r => StoredForestCandidate.typedResult fs r.bank r.edge w t

theorem execute_encoded {n : ℕ} (fs : List (List (Fin n × Fin n))) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (rs : List (TypedInput n)) :
    execute n (fs.map StoredEdges.encode) (StoredRecords.encodeWeights w) t (rs.map encode)=
      (typedValue fs w t rs).map StoredCandidates.encode := by
  rw [execute_eq]
  simp only [value,typedValue,List.map_map,Function.comp_def,encode,StoredForestCandidate.value_encoded]
end LightEFTSpanners.StoredForestBank
