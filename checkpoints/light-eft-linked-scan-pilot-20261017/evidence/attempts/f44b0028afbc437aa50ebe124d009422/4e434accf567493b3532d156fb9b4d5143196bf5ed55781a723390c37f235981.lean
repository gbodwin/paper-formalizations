import LightEFTSpanners.StoredGraphMatrixBound

namespace LightEFTSpanners.StoredEdgeComponent
open Controller
inductive State where
  | matrix : StoredGraphMatrix.State → State
  | component : LinkedDistance.Matrix → StoredComponentDiscovery.State → State
  | halt : List ℕ → State
  deriving DecidableEq, Repr

def transition (n root : ℕ) (edges : List StoredEdges.Edge) : State → Option State
  | .matrix (.halt M) => some (.component M (.enumerate n []))
  | .matrix s => (StoredGraphMatrix.transition n edges s).map State.matrix
  | .component _ (.halt out) => some (.halt out)
  | .component M s => (StoredComponentDiscovery.transition n M root s).map (State.component M)
  | .halt _ => none

theorem matrix_lift (n root : ℕ) (edges : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredGraphMatrix.State} (h : Trace (StoredGraphMatrix.transition n edges) k s t) :
    Trace (transition n root edges) k (.matrix s) (.matrix t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredGraphMatrix.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.matrix) he

theorem component_lift (n root : ℕ) (edges : List StoredEdges.Edge) (M : LinkedDistance.Matrix)
    {k : ℕ} {s t : StoredComponentDiscovery.State}
    (h : Trace (StoredComponentDiscovery.transition n M root) k s t) :
    Trace (transition n root edges) k (.component M s) (.component M t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredComponentDiscovery.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map (State.component M)) he

def bound (n m : ℕ) : ℕ := StoredGraphMatrix.bound n m+StoredComponentDiscovery.bound n+2

def execute (n root : ℕ) (edges : List StoredEdges.Edge) : List ℕ :=
  match Controller.run (transition n root edges) (bound n edges.length) (.matrix (.zero (.row n []))) with
  | .halt out => out
  | _ => []

theorem constructed_trace {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    ∃ k,k≤bound n edges.length ∧ Trace (transition n root.val (StoredEdges.encode edges)) k
      (.matrix (.zero (.row n [])))
      (.halt (StoredReachability.values (ExecutableVoting.graph (StoredSample.edgeSet edges)) root (List.finRange n))) := by
  let es := StoredEdges.encode edges
  let G := ExecutableVoting.graph (StoredSample.edgeSet edges)
  let M := LinkedDistance.matrixOf G (fun _ => 0)
  have a := matrix_lift n root.val es (StoredGraphMatrix.constructed_trace n es)
  have hM : StoredGraphMatrix.value n es=M := StoredGraphMatrix.value_encoded edges
  rw [hM] at a
  obtain ⟨k,hk,ht⟩ := StoredComponentDiscovery.constructed_trace G root
  have b := component_lift n root.val es M ht
  have x := Trace.one (show transition n root.val es (.matrix (.halt M))=
    some (.component M (.enumerate n [])) from rfl)
  have y := Trace.one (show transition n root.val es
    (.component M (.halt (StoredReachability.values G root (List.finRange n))))=
      some (.halt (StoredReachability.values G root (List.finRange n))) from rfl)
  refine ⟨StoredGraphMatrix.steps n es+1+k+1,?_,?_⟩
  · have hb := StoredGraphMatrix.steps_le n es
    have he : es.length=edges.length := by simp [es,StoredEdges.encode]
    rw [he] at hb
    unfold bound
    omega
  · simpa only [Nat.add_assoc] using a.trans (x.trans (b.trans y))

theorem execute_eq {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    execute n root.val (StoredEdges.encode edges)=
      StoredReachability.values (ExecutableVoting.graph (StoredSample.edgeSet edges)) root (List.finRange n) := by
  obtain ⟨k,hk,ht⟩ := constructed_trace edges root
  have he : bound n (StoredEdges.encode edges).length=k+(bound n (StoredEdges.encode edges).length-k) := by
    simp only [StoredEdges.encode,List.length_map]
    omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

theorem execute_mem {n : ℕ} (edges : List (Fin n × Fin n)) (root v : Fin n) :
    v.val∈execute n root.val (StoredEdges.encode edges) ↔
      (ExecutableVoting.graph (StoredSample.edgeSet edges)).Reachable root v := by
  rw [execute_eq,StoredReachability.mem_values]
  simp
end LightEFTSpanners.StoredEdgeComponent
