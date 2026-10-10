import DirectedFlowCutGap.BinaryFractionalGraphOracle
import DirectedFlowCutGap.BinaryFractionalWalkBounds

/-!
# Concrete minimum-column oracle charges

The actual vertex adapter instantiates every cost callback with retained row
reads. Bounds cover all demand paths, comparisons, Boolean-mask construction,
and the independent resource scan for the bottleneck. The capacity width and
current covering-weight width are separate parameters; no operand-width or
oracle-runtime premise is hidden in the concluding oracle theorem.
-/
namespace DirectedFlowCutGap.BinaryFractionalGraphBounds
open BinaryRational BinaryFractionalRows BinaryFractionalWalkOracle
open BinaryFractionalGraphOracle BinaryFractionalWalkBounds
open IntegralNetworkFlow
variable {n m B W C : ℕ}

theorem read_charge (y : Row m) (i : Fin m) : (read y i).2=7 := rfl

theorem outgoing_stored (y : Row n) (hy : ∀ i, StoredBounded (get y i) B)
    (s : Fin n) (e : Pair n) : StoredBounded (outgoing y s e).1 (B+1) := by
  unfold outgoing
  split
  · exact stored_mono zero_stored (Nat.le_add_left 1 B)
  · exact stored_mono (hy e.1) (Nat.le_succ B)

theorem outgoing_charge (y : Row n) (s : Fin n) (e : Pair n) :
    (outgoing y s e).2≤13 := by
  unfold outgoing
  split <;> simp [read_charge]

def OptionProperty {α : Type*} (P : α → Prop) (q : Option α) : Prop :=
  ∀ x, q=some x → P x

theorem argminAux_property {α : Type*} (score : α → Fraction × ℕ) (P : α → Prop)
    (a : Option α) (x : α) (ha : OptionProperty P a) (hx : P x) :
    OptionProperty P (argminAux score a x).1 := by
  cases a with
  | none => intro z hz; cases hz; exact hx
  | some a =>
    intro z hz
    simp only [argminAux] at hz
    split at hz
    · cases hz; exact hx
    · cases hz; exact ha a rfl

theorem argminFrom_property {α : Type*} (score : α → Fraction × ℕ) (P : α → Prop)
    (xs : List α) (acc : Option α) (hxs : ∀ x ∈ xs, P x) (ha : OptionProperty P acc) :
    OptionProperty P (argminFrom score xs acc).1 := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    exact ih _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      (argminAux_property score P acc x ha (hxs x List.mem_cons_self))

theorem argmin_property {α : Type*} (score : α → Fraction × ℕ) (P : α → Prop)
    (xs : List α) (hxs : ∀ x ∈ xs, P x) : OptionProperty P (argmin score xs).1 :=
  argminFrom_property score P xs none hxs (fun _ h => by cases h)

theorem argminAux_charge {α : Type*} (score : α → Fraction × ℕ)
    (acc : Option α) (x : α)
    (ha : OptionProperty (fun z => StoredBounded (score z).1 B ∧ (score z).2≤ C) acc)
    (hx : StoredBounded (score x).1 B ∧ (score x).2≤ C) :
    (argminAux score acc x).2 ≤ 2*C+2048*(B+1)^2+8 := by
  cases acc with
  | none => simp [argminAux]
  | some a =>
    have hs := ha a rfl
    have hl := le_charge hs.1 hx.1
    simp only [argminAux]
    omega

def argminBound (N B C : ℕ) : ℕ := N*(2*C+2048*(B+1)^2+12)+1

theorem argminFrom_charge {α : Type*} (score : α → Fraction × ℕ)
    (xs : List α) (acc : Option α)
    (hxs : ∀ x ∈ xs, StoredBounded (score x).1 B ∧ (score x).2≤ C)
    (ha : OptionProperty (fun z => StoredBounded (score z).1 B ∧ (score z).2≤ C) acc) :
    (argminFrom score xs acc).2 ≤ argminBound xs.length B C := by
  induction xs generalizing acc with
  | nil => simp [argminFrom,argminBound]
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    have hq := argminAux_charge score acc x ha hx
    have hp := argminAux_property score _ acc x ha hx
    have ht := ih _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hp
    simp only [argminFrom,List.length_cons]
    unfold argminBound at *
    nlinarith

theorem argmin_charge {α : Type*} (score : α → Fraction × ℕ) (xs : List α)
    (hxs : ∀ x ∈ xs, StoredBounded (score x).1 B ∧ (score x).2≤ C) :
    (argmin score xs).2 ≤ argminBound xs.length B C :=
  argminFrom_charge score xs none hxs (fun _ h => by cases h)

theorem argminBound_mono {a b B C : ℕ} (h : a≤ b) :
    argminBound a B C≤ argminBound b B C :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 1

theorem shortest_edges_length (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n)
    {q : Candidate n} (hq : (shortest E adjacency cost s t).1=some q) : q.edges.length≤ n := by
  unfold shortest at hq
  dsimp only at hq
  split at hq
  · cases hq
  · rename_i p _
    cases hq
    simpa only [recover,Fintype.card_fin] using
      (IntegralNetworkFlow.Tabulated.RetainedPathSearch.search E
        (supportTest adjacency p.edges) s t).edges_length_le

def SelectedStored (q : Selected n) (W : ℕ) : Prop :=
  StoredBounded q.path.cost W ∧ q.path.edges.length≤ n

theorem collect_properties (adjacency : Adjacency n) (y : Row n)
    (hy : ∀ i, StoredBounded (get y i) B) (ds : List (Pair n)) :
    ∀ q ∈ (collect adjacency y ds).1, SelectedStored q (n*(B+2)+1) := by
  induction ds with
  | nil => intro q hq; cases hq
  | cons d ds ih =>
    intro q hq
    simp only [collect] at hq
    split at hq
    · exact ih q hq
    · rename_i p hp
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨shortest_stored _ adjacency (outgoing y d.1) (outgoing_stored y hy d.1)
          d.1 d.2 p hp,shortest_edges_length _ adjacency (outgoing y d.1) d.1 d.2 hp⟩
      · exact ih q hq

theorem collect_length (adjacency : Adjacency n) (y : Row n) (ds : List (Pair n)) :
    (collect adjacency y ds).1.length≤ ds.length := by
  induction ds with
  | nil => simp [collect]
  | cons d ds ih =>
    simp only [collect,List.length_cons]
    split <;> simp only [List.length_cons] <;> omega

def collectBound (n D B : ℕ) : ℕ := D*(shortestBound n (B+1) 13+10)+1

theorem collect_charge (adjacency : Adjacency n) (y : Row n)
    (hy : ∀ i, StoredBounded (get y i) B) (ds : List (Pair n)) :
    (collect adjacency y ds).2 ≤ collectBound n ds.length B := by
  induction ds with
  | nil => simp [collect,collectBound]
  | cons d ds ih =>
    have h := shortest_charge (ResidualSearch.Enumeration.fin n) adjacency (outgoing y d.1)
      (outgoing_stored y hy d.1) (outgoing_charge y d.1) d.1 d.2
    simp only [collect,List.length_cons]
    split <;> unfold collectBound at * <;> nlinarith

def selectedBound (n D B : ℕ) : ℕ :=
  collectBound n D B+argminBound D (n*(B+2)+1) 4+4

theorem selected_properties (adjacency : Adjacency n) (y : Row n)
    (hy : ∀ i, StoredBounded (get y i) B) (ds : List (Pair n)) :
    OptionProperty (fun q => SelectedStored q (n*(B+2)+1)) (selected adjacency y ds).1 :=
  argmin_property _ _ _ (collect_properties adjacency y hy ds)

theorem selected_charge (adjacency : Adjacency n) (y : Row n)
    (hy : ∀ i, StoredBounded (get y i) B) (ds : List (Pair n)) :
    (selected adjacency y ds).2 ≤ selectedBound n ds.length B := by
  have hc := collect_charge adjacency y hy ds
  have hl := collect_length adjacency y ds
  have ha := argmin_charge (fun q : Selected n => (q.path.cost,4)) (collect adjacency y ds).1
    (fun q hq => ⟨(collect_properties adjacency y hy ds q hq).1,le_rfl⟩)
  have hm := argminBound_mono (B := n*(B+2)+1) (C := 4) hl
  unfold selected selectedBound
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add hc (ha.trans hm)) 4

theorem memberTail_charge (i : Fin n) (es : List (Pair n)) :
    (memberTail i es).2 ≤ 6*es.length+1 := by
  induction es with
  | nil => simp [memberTail]
  | cons e es ih =>
    simp only [memberTail,List.length_cons]
    split <;> dsimp only <;> omega

def maskBound (n L : ℕ) : ℕ := n*(6*L+9)+EncodedRoundingInput.arrayBound n

theorem internalMask_charge (s t : Fin n) (es : List (Pair n)) :
    (internalMask s t es).2 ≤ maskBound n es.length := by
  apply EncodedRoundingInput.tabulate_bound _ (6*es.length+9)
  intro i
  have h := memberTail_charge i es
  split <;> dsimp only <;> omega

theorem indices_length (mask : Vector Bool m) (is : List (Fin m)) :
    (indices mask is).1.length≤ is.length := by
  induction is with
  | nil => simp [indices]
  | cons i is ih =>
    simp only [indices,List.length_cons]
    split <;> simp only [List.length_cons] <;> omega

theorem indices_charge (mask : Vector Bool m) (is : List (Fin m)) :
    (indices mask is).2 ≤ 8*is.length+1 := by
  induction is with
  | nil => simp [indices]
  | cons i is ih =>
    simp only [indices,List.length_cons]
    split <;> dsimp only <;> omega

def bottleneckBound (m B : ℕ) : ℕ := 16*m+argminBound m B 7+5

/-- This resource scan uses m, independently of the graph vertex dimension n. -/
theorem bottleneck_charge (c : Row m) (hc : ∀ i, StoredBounded (get c i) B)
    (mask : Vector Bool m) : (bottleneck c mask).2 ≤ bottleneckBound m B := by
  have hi := indices_charge mask (List.finRange m)
  have hl := indices_length mask (List.finRange m)
  simp only [List.length_finRange] at hi hl
  have ha := argmin_charge (B := B) (C := 7) (read c) (indices mask (List.finRange m)).1
    (fun i _ => ⟨hc i,le_rfl⟩)
  have hm := argminBound_mono (B := B) (C := 7) hl
  unfold bottleneck bottleneckBound
  dsimp only
  omega

theorem singletonMask_charge (i : Fin m) :
    (singletonMask i).2 ≤ 4*m+EncodedRoundingInput.arrayBound m := by
  have h := EncodedRoundingInput.tabulate_bound (fun j : Fin m => (decide (j=i),4)) 4
    (fun _ => le_rfl)
  simpa only [singletonMask,Nat.mul_comm m 4] using h

def oracleBound (n D capacityWidth weightWidth : ℕ) : ℕ :=
  selectedBound n D weightWidth+maskBound n n+bottleneckBound n capacityWidth+8

/-- Every callback is now instantiated with the actual graph program. -/
theorem oracle_charge (adjacency : Adjacency n) (ds : List (Pair n))
    (c y : Row n) (hn : 0<n)
    (hc : ∀ i, StoredBounded (get c i) B) (hy : ∀ i, StoredBounded (get y i) W) :
    (oracle adjacency ds c hn y).2 ≤ oracleBound n ds.length B W := by
  have hs := selected_charge adjacency y hy ds
  unfold oracle
  dsimp only
  split
  · have hm := singletonMask_charge (⟨0,hn⟩ : Fin n)
    unfold oracleBound maskBound
    nlinarith
  · rename_i q hq
    have hp := (selected_properties adjacency y hy ds q hq).2
    have hm := internalMask_charge q.demand.1 q.demand.2 q.path.edges
    have hb := bottleneck_charge c hc (internalMask q.demand.1 q.demand.2 q.path.edges).1
    have hmono : maskBound n q.path.edges.length≤ maskBound n n := by
      unfold maskBound
      nlinarith
    unfold oracleBound
    omega

end DirectedFlowCutGap.BinaryFractionalGraphBounds
