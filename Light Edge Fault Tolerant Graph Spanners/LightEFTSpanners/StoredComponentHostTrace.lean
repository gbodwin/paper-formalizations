import LightEFTSpanners.StoredComponentHostFilter

namespace LightEFTSpanners.StoredComponentHostFilter
open Controller

def value (vs : List ℕ) (es : List StoredEdges.Edge) : List StoredEdges.Edge := es.filter (selected vs)
def scanSteps (vs : List ℕ) : List StoredEdges.Edge → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun e _ rest => edgeSteps vs e+rest)

theorem scanSteps_nil (vs : List ℕ) : scanSteps vs [] = 1 := rfl

theorem scanSteps_cons (vs : List ℕ) (e : StoredEdges.Edge) (es : List StoredEdges.Edge) :
    scanSteps vs (e::es) = edgeSteps vs e+scanSteps vs es := rfl

theorem scan_trace (vs : List ℕ) (es acc : List StoredEdges.Edge) :
    Trace (transition vs) (scanSteps vs es) (.edges es acc)
      (.reverse ((value vs es).reverse++acc) []) := by
  induction es generalizing acc with
  | nil => exact Trace.one rfl
  | cons e es ih =>
    have a := edge_trace vs e es acc
    have b := ih (if selected vs e then e::acc else acc)
    cases h : selected vs e <;>
      simpa [scanSteps_cons,value,h,List.reverse_cons,List.append_assoc] using a.trans b

theorem reverse_trace (vs : List ℕ) (es out : List StoredEdges.Edge) :
    Trace (transition vs) (es.length+1) (.reverse es out) (.halt (es.reverse++out)) := by
  induction es generalizing out with
  | nil => exact Trace.one rfl
  | cons e es ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition vs (.reverse (e::es) out)=some (.reverse es (e::out)) from rfl) (ih (e::out))

def steps (vs : List ℕ) (es : List StoredEdges.Edge) : ℕ := scanSteps vs es+(value vs es).length+1

theorem filter_trace (vs : List ℕ) (es : List StoredEdges.Edge) :
    Trace (transition vs) (steps vs es) (.edges es []) (.halt (value vs es)) := by
  have a := scan_trace vs es []
  simp only [List.append_nil] at a
  have b := reverse_trace vs (value vs es).reverse []
  simpa [steps,Nat.add_assoc] using a.trans b

theorem edgeSteps_le (vs : List ℕ) (e : StoredEdges.Edge) : edgeSteps vs e≤2*vs.length+5 := by
  have h₁ := StoredVertexMembership.steps_le e.1 vs
  have h₂ := StoredVertexMembership.steps_le e.2 vs
  unfold edgeSteps
  split
  · omega
  · split <;> omega

theorem scanSteps_le (vs : List ℕ) (es : List StoredEdges.Edge) :
    scanSteps vs es≤es.length*(2*vs.length+5)+1 := by
  induction es with
  | nil => simp [scanSteps_nil]
  | cons e es ih =>
    have h := edgeSteps_le vs e
    simp only [scanSteps_cons,List.length_cons,Nat.add_mul]
    omega

def bound (n m : ℕ) : ℕ := m*(2*n+6)+2

theorem steps_le (vs : List ℕ) (es : List StoredEdges.Edge) : steps vs es≤bound vs.length es.length := by
  have h := scanSteps_le vs es
  have hl : (value vs es).length≤es.length := List.length_filter_le _ _
  unfold steps bound
  have he : es.length*(2*vs.length+6)=es.length*(2*vs.length+5)+es.length := by ring
  rw [he]
  omega
end LightEFTSpanners.StoredComponentHostFilter
