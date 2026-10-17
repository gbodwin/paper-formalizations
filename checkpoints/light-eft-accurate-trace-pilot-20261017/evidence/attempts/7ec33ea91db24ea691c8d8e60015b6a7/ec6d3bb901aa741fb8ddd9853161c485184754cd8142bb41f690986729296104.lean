import LightEFTSpanners.StoredCanonicalRepresentative

namespace LightEFTSpanners.StoredCanonicalRoot
open Controller StoredCanonicalComponents
inductive State where
  | component : StoredEdgeComponent.State → State
  | minimum : List ℕ → StoredVertexMinimum.State → State
  | halt : Option (List ℕ) → State
  deriving DecidableEq, Repr

def transition (n root : ℕ) (edges : List StoredEdges.Edge) : State → Option State
  | .component (.halt vs) => some (.minimum vs (.scan vs root))
  | .component s => (StoredEdgeComponent.transition n root edges s).map State.component
  | .minimum vs (.halt best) => some (.halt (if best=root then some vs else none))
  | .minimum vs s => (StoredVertexMinimum.transition s).map (State.minimum vs)
  | .halt _ => none

theorem component_lift (n root : ℕ) (edges : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredEdgeComponent.State} (h : Trace (StoredEdgeComponent.transition n root edges) k s t) :
    Trace (transition n root edges) k (.component s) (.component t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredEdgeComponent.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.component) he

theorem minimum_lift (n root : ℕ) (edges : List StoredEdges.Edge) (vs : List ℕ)
    {k : ℕ} {s t : StoredVertexMinimum.State} (h : Trace StoredVertexMinimum.transition k s t) :
    Trace (transition n root edges) k (.minimum vs s) (.minimum vs t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredVertexMinimum.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map (State.minimum vs)) he

def result {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) : Option (List ℕ) :=
  if least edges root=root.val then some ((StoredEdgeComponent.vertices edges root).map Fin.val) else none

def bound (n m : ℕ) : ℕ := StoredEdgeComponent.bound n m+n+3

theorem root_trace {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    ∃ k,k≤bound n edges.length ∧ Trace (transition n root.val (StoredEdges.encode edges)) k
      (.component (.matrix (.zero (.row n [])))) (.halt (result edges root)) := by
  let vs := (StoredEdgeComponent.vertices edges root).map Fin.val
  obtain ⟨k,hk,ht⟩ := StoredEdgeComponent.constructed_trace edges root
  have a := component_lift n root.val (StoredEdges.encode edges) ht
  change Trace (transition n root.val (StoredEdges.encode edges)) k _ (.component (.halt vs)) at a
  have b := minimum_lift n root.val (StoredEdges.encode edges) vs (StoredVertexMinimum.scan_trace vs root.val)
  have x := Trace.one (show transition n root.val (StoredEdges.encode edges) (.component (.halt vs))=
    some (.minimum vs (.scan vs root.val)) from rfl)
  have y := Trace.one (show transition n root.val (StoredEdges.encode edges)
    (.minimum vs (.halt (StoredVertexMinimum.value vs root.val)))=some (.halt (result edges root)) from rfl)
  have hl : vs.length≤n := by
    simpa [vs,StoredEdgeComponent.vertices] using
      List.length_filter_le (StoredReachability.test (ExecutableVoting.graph (StoredSample.edgeSet edges)) root) (List.finRange n)
  refine ⟨k+1+(vs.length+1)+1,?_,?_⟩
  · unfold bound
    omega
  · simpa only [Nat.add_assoc] using a.trans (x.trans (b.trans y))

theorem result_some_iff {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    (result edges root).isSome=true ↔ root∈roots edges := by
  rw [mem_roots]
  simp [result,representative,Fin.ext_iff]
end LightEFTSpanners.StoredCanonicalRoot
