import DirectedFlowCutGap.RationalEdgeThresholds
import DirectedFlowCutGap.BinaryFractionalWalkBounds

/-! Compute the threshold-demand list and record the exact binary path and
comparison charges on the original stored weights. -/

namespace DirectedFlowCutGap.ChargedEdgeThresholdDemands

open BinaryFractionalWalkOracle BinaryFractionalWalkBounds BinaryRational
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open RationalEdgeThresholds (Weights cost)

def far {n : ℕ} (adj : Adjacency n) (w : Weights n) (p : Fin n × Fin n) : Bool × ℕ :=
  let route := shortest (ResidualSearch.Enumeration.fin n) adj (cost w) p.1 p.2
  match route.1 with
  | none => (true,route.2+4)
  | some path =>
    let cmp := BinaryRational.le one path.cost
    (cmp.1,route.2+cmp.2+4)

private theorem far_value {n : ℕ} (adj : Adjacency n) (w : Weights n) (p : Fin n × Fin n) :
    (far adj w p).1=RationalEdgeThresholds.far adj w p := by
  unfold far RationalEdgeThresholds.far
  dsimp only
  cases h : (shortest (ResidualSearch.Enumeration.fin n) adj (cost w) p.1 p.2).1 <;> rfl

def pairBudget (n B : ℕ) : ℕ := shortestBound n B 2+2048*(n*(B+1)+2)^2+4

theorem far_paid {n B : ℕ} (adj : Adjacency n) (w : Weights n)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) (p : Fin n × Fin n) :
    (far adj w p).2 ≤ pairBudget n B := by
  let E := ResidualSearch.Enumeration.fin n
  let route := shortest E adj (cost w) p.1 p.2
  have width : ∀ e, StoredBounded (cost w e).1 B := fun e => fits e.1 e.2
  have h : route.2 ≤ shortestBound n B 2 := shortest_charge E adj (cost w) width (C:=2) (fun _ => le_rfl) p.1 p.2
  have result := shortest_stored E adj (cost w) width p.1 p.2
  change (match route.1 with
    | none => (true,route.2+4)
    | some path => ((BinaryRational.le one path.cost).1,route.2+(BinaryRational.le one path.cost).2+4)).2 ≤ pairBudget n B
  unfold pairBudget
  split
  · dsimp only
    omega
  next path call =>
    have oneWidth : StoredBounded one (n*(B+1)+1) := by
      unfold StoredBounded one
      simp
    have cmp := le_charge oneWidth (result path call)
    exact Nat.add_le_add_right (Nat.add_le_add h cmp) 4

private def collect {n : ℕ} (adj : Adjacency n) (w : Weights n) :
    List (Fin n × Fin n) → List (Fin n × Fin n) × ℕ
  | [] => ([],1)
  | p::ps =>
    let test := far adj w p
    let more := collect adj w ps
    (if test.1 then p::more.1 else more.1,test.2+more.2+6)

private theorem collect_value {n : ℕ} (adj : Adjacency n) (w : Weights n) (ps : List (Fin n × Fin n)) :
    (collect adj w ps).1=ps.filter (RationalEdgeThresholds.far adj w) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [collect,far_value,ih,List.filter_cons]

private theorem collect_paid {n B : ℕ} (adj : Adjacency n) (w : Weights n)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) (ps : List (Fin n × Fin n)) :
    (collect adj w ps).2 ≤ ps.length*(pairBudget n B+6)+1 := by
  induction ps with
  | nil => simp [collect]
  | cons p ps ih =>
    have charge := far_paid adj w fits p
    simp only [collect,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun s => (List.finRange n).map fun t => (s,t)

def demands {n : ℕ} (adj : Adjacency n) (w : Weights n) : List (Fin n × Fin n) × ℕ :=
  let out := collect adj w (pairs n)
  (out.1,out.2+12*n*n+10*n+5)

theorem demands_value {n : ℕ} (adj : Adjacency n) (w : Weights n) :
    (demands adj w).1=RationalEdgeThresholds.demands adj w := collect_value adj w (pairs n)

def demandBudget (n B : ℕ) : ℕ := n*n*(pairBudget n B+6)+1+12*n*n+10*n+5

theorem demands_paid {n B : ℕ} (adj : Adjacency n) (w : Weights n)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) :
    (demands adj w).2 ≤ demandBudget n B := by
  have h := collect_paid adj w fits (pairs n)
  have len : (pairs n).length=n*n := by simp [pairs,List.length_flatMap]
  rw [len] at h
  unfold demands demandBudget
  dsimp only
  omega

end DirectedFlowCutGap.ChargedEdgeThresholdDemands
