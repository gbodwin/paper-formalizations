import LightEFTSpanners.StoredReachabilityTrace

namespace LightEFTSpanners.StoredComponentDiscovery
open Controller
inductive State where
  | enumerate : ℕ → List ℕ → State
  | search : StoredReachability.State → State
  | halt : List ℕ → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (M : LinkedDistance.Matrix) (root : ℕ) : State → Option State
  | .enumerate 0 acc => some (.search (.scan acc []))
  | .enumerate (k+1) acc => some (.enumerate k (k::acc))
  | .search (.halt out) => some (.halt out)
  | .search s => (StoredReachability.transition n M root s).map State.search
  | .halt _ => none

theorem enumerate_trace (n : ℕ) (M : LinkedDistance.Matrix) (root k : ℕ) (acc : List ℕ) :
    Trace (transition n M root) (k+1) (.enumerate k acc)
      (.search (.scan (List.range k++acc) [])) := by
  induction k generalizing acc with
  | zero => exact Trace.one rfl
  | succ k ih =>
    simpa [List.range_succ,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n M root (.enumerate (k+1) acc)=some (.enumerate k (k::acc)) from rfl)
        (ih (k::acc))

theorem search_lift (n : ℕ) (M : LinkedDistance.Matrix) (root : ℕ)
    {k : ℕ} {s t : StoredReachability.State} (h : Trace (StoredReachability.transition n M root) k s t) :
    Trace (transition n M root) k (.search s) (.search t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredReachability.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.search) he

def bound (n : ℕ) : ℕ := n+StoredReachability.bound n n+2

def execute (n : ℕ) (M : LinkedDistance.Matrix) (root : ℕ) : List ℕ :=
  match Controller.run (transition n M root) (bound n) (.enumerate n []) with
  | .halt vs => vs
  | _ => []

theorem constructed_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root : Fin n) :
    ∃ k,k≤bound n ∧ Trace (transition n (LinkedDistance.matrixOf G (fun _ => 0)) root.val) k
      (.enumerate n []) (.halt (StoredReachability.values G root (List.finRange n))) := by
  have a := enumerate_trace n (LinkedDistance.matrixOf G (fun _ => 0)) root.val n []
  obtain ⟨k,hk,h⟩ := StoredReachability.component_trace G root (List.finRange n)
  have b := search_lift n (LinkedDistance.matrixOf G (fun _ => 0)) root.val h
  have c := Trace.one (show transition n (LinkedDistance.matrixOf G (fun _ => 0)) root.val
    (.search (.halt (StoredReachability.values G root (List.finRange n))))=
      some (.halt (StoredReachability.values G root (List.finRange n))) from rfl)
  have he : (List.finRange n).map Fin.val=List.range n := by simp
  rw [he] at b
  simp only [List.append_nil] at a
  refine ⟨n+1+k+1,?_,?_⟩
  · simp only [List.length_finRange] at hk
    unfold bound
    omega
  · simpa only [Nat.add_assoc] using a.trans (b.trans c)

theorem execute_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (root : Fin n) :
    execute n (LinkedDistance.matrixOf G (fun _ => 0)) root.val=
      StoredReachability.values G root (List.finRange n) := by
  obtain ⟨k,hk,ht⟩ := constructed_trace G root
  have he : bound n=k+(bound n-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

theorem execute_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (root v : Fin n) :
    v.val∈execute n (LinkedDistance.matrixOf G (fun _ => 0)) root.val ↔ G.Reachable root v := by
  rw [execute_eq,StoredReachability.mem_values]
  simp
end LightEFTSpanners.StoredComponentDiscovery
