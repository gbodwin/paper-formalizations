import DirectedFlowCutGap.ConcurrentEdgeCoverPathWork
import DirectedFlowCutGap.ConcurrentEdgeBudgetWidths

/-! Sum the actual binary shortest-path work through every generated
positive budget candidate. The selected plan is unchanged. -/
namespace DirectedFlowCutGap.ConcurrentEdgeBudgetPathWork

open scoped NNRat
open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open ConcurrentEdgeBudgetSelection (Plan plan)
open ConcurrentEdgeBudgetGrid (pairs)
open ConcurrentEdgeCoverPathWork (searchBound)
open ConcurrentEdgeBudgetWidths (priceWidth massWidth)

variable {m n : ℕ}

def measuredCandidates (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    List (Weights n × ℕ) :=
  (pairs A c m).map fun (B,U) => ConcurrentEdgeCoverPathWork.solve hn A
    (ConcurrentEdgeMassBudget.reprice c B U) P

theorem candidates_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (measuredCandidates hn A c P).map Prod.fst = ConcurrentEdgeBudgetGrid.candidates hn A c P := by
  unfold measuredCandidates ConcurrentEdgeBudgetGrid.candidates
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  rcases p with ⟨B,U⟩
  exact ConcurrentEdgeCoverPathWork.solve_value hn A _ P

def choose (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (Plan n) × ℕ :=
  let jobs := measuredCandidates hn A c P
  (((jobs.map Prod.fst).map fun w => plan A c w m).argmin Plan.receipt,(jobs.map Prod.snd).sum)

theorem choose_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (choose hn A c P).1 = ConcurrentEdgeBudgetSelection.choose hn A c P := by
  unfold choose ConcurrentEdgeBudgetSelection.choose
  dsimp only
  rw [candidates_value]

private theorem sum_le_length {α : Type*} (items : List α) (f : α → ℕ) (bound : ℕ)
    (each : ∀ i ∈ items, f i ≤ bound) : (items.map f).sum ≤ items.length*bound := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    have a := each first List.mem_cons_self
    have b := ih (fun j found => each j (List.mem_cons_of_mem _ found))
    omega

def chooseSearchBound (n m L : ℕ) : ℕ :=
  ((n*n*L+(m+n*n*(L+1))+3)*(m+n*2+3))*searchBound n m (L+priceWidth n m L+massWidth n m+2)

theorem choose_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {L : ℕ} (input : MatrixFits c L) : (choose hn A c P).2 ≤ chooseSearchBound n m L := by
  let jobs := measuredCandidates hn A c P
  let bound := searchBound n m (L+priceWidth n m L+massWidth n m+2)
  have each (j : Weights n × ℕ) (present : j ∈ jobs) : j.2 ≤ bound := by
    obtain ⟨⟨B,U⟩,pair,rfl⟩ := List.mem_map.mp present
    have fit := ConcurrentEdgeBudgetWidths.pair_fits A c m input pair
    exact ConcurrentEdgeCoverPathWork.solve_charge hn A _ P
      (ConcurrentEdgeCoverWidths.reprice_fits c B U input fit.1 fit.2)
  have size : jobs.length ≤ (n*n*L+(m+n*n*(L+1))+3)*(m+n*2+3) := by
    simp only [jobs,measuredCandidates,List.length_map]
    exact ConcurrentEdgeBudgetWidths.pair_count A c m input
  exact (sum_le_length jobs Prod.snd bound each).trans (Nat.mul_le_mul_right bound size)

end DirectedFlowCutGap.ConcurrentEdgeBudgetPathWork
