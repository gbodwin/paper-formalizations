import DirectedFlowCutGap.BinaryFractionalGraphOracle

namespace DirectedFlowCutGap.BinaryFractionalWalkOracle
open BinaryRational IntegralNetworkFlow IntegralNetworkFlow.Tabulated
variable {n : ℕ}

theorem extend_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1) (u v : Fin n) (q : Candidate n) :
    (extend a u v q).1=(extend b u v q).1 := by simp only [extend,h]

theorem scan_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (adjacency : Adjacency n) (u : Fin n) (xs : Table n) :
    (scan adjacency a u xs).1=(scan adjacency b u xs).1 := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨v,q⟩
    simp only [scan]
    split <;> simp only [ih,extend_cost_eq a b h]

theorem atVertex_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (adjacency : Adjacency n) (t u : Fin n) (old : Table n) :
    (atVertex adjacency a t u old).1=(atVertex adjacency b t u old).1 := by
  unfold atVertex
  split <;> simp only [scan_cost_eq a b h]

theorem pass_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (adjacency : Adjacency n) (t : Fin n) (old : Table n) (vs : List (Fin n)) :
    (pass adjacency a t old vs).1=(pass adjacency b t old vs).1 := by
  induction vs with
  | nil => rfl
  | cons u us ih =>
    simp only [pass,atVertex_cost_eq a b h]
    cases (atVertex adjacency b t u old).1 <;> simp only [ih]

theorem rounds_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (vs : List (Fin n)) (adjacency : Adjacency n) (t : Fin n) (fuel : List (Fin n)) :
    (rounds vs adjacency a t fuel).1=(rounds vs adjacency b t fuel).1 := by
  induction fuel with
  | nil => rfl
  | cons u us ih => simp only [rounds,ih,pass_cost_eq a b h]

theorem minimize_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n) (s t : Fin n) :
    (minimize E adjacency a s t).1=(minimize E adjacency b s t).1 := by
  simp only [minimize,rounds_cost_eq a b h]

theorem costList_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1) (es : List (Pair n)) :
    (costList a es).1=(costList b es).1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [costList,h,ih]

theorem recover_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n) (s t : Fin n) (es : List (Pair n)) :
    (recover E adjacency a s t es).1=(recover E adjacency b s t es).1 := by
  simp only [recover,costList_cost_eq a b h]

theorem shortest_cost_eq (a b : Cost n) (h : ∀ e,(a e).1=(b e).1)
    (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n) (s t : Fin n) :
    (shortest E adjacency a s t).1=(shortest E adjacency b s t).1 := by
  simp only [shortest,minimize_cost_eq a b h]
  cases (minimize E adjacency b s t).1 <;> simp only [recover_cost_eq a b h]
end DirectedFlowCutGap.BinaryFractionalWalkOracle
