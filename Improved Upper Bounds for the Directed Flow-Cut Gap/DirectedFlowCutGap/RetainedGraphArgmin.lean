import DirectedFlowCutGap.RetainedArgminProgram
import DirectedFlowCutGap.BinaryFractionalGraphOracle

/-! The actual retained-record selector implements the existing graph oracle's
stable argmin value. Each encoded record keeps its literal address and opaque
payload; the score is the retained path cost. Heap construction and computing
those path costs remain separate. Concrete instruction charges are used here,
not the older abstract score-read charges. -/
namespace DirectedFlowCutGap.RetainedGraphArgmin
open RetainedArgminProgram ImmutableReferenceSimulation ImmutableReferenceTerminal BinaryArithmetic


def item {α : Type*} (score : α → BinaryRational.Fraction × ℕ)
    (payload address : α → ℕ) (x : α) : Item :=
  ⟨(score x).1,payload x,address x⟩

theorem from_refines {α : Type*} (score : α → BinaryRational.Fraction × ℕ)
    (payload address : α → ℕ) (xs : List α) (a : α) :
    some (selectFrom (item score payload address a) (xs.map (item score payload address)))=
      (BinaryFractionalGraphOracle.argminFrom score xs (some a)).1.map (item score payload address) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,selectFrom,choose,keep,item,
      BinaryFractionalGraphOracle.argminFrom,BinaryFractionalGraphOracle.argminAux]
    by_cases hc : (BinaryRational.le (score a).1 (score x).1).1=true
    · simpa only [item,hc,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
        using ih a
    · have hf : (BinaryRational.le (score a).1 (score x).1).1=false :=
        Bool.eq_false_iff.mpr hc
      simpa only [item,hf,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
        using ih x

theorem value_refines {α : Type*} (score : α → BinaryRational.Fraction × ℕ)
    (payload address : α → ℕ) (xs : List α) :
    select (xs.map (item score payload address))=
      (BinaryFractionalGraphOracle.argmin score xs).1.map (item score payload address) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    exact from_refines score payload address xs x

/-- Exactly the existing retained-demand/path selection, including its first
minimum tie rule. No minimum-value-only or reconstructed-payload surrogate is
substituted for the graph oracle's chosen record. -/
theorem selected_refines {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (payload address : BinaryFractionalGraphOracle.Selected n → ℕ) :
    select (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map
      (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address))=
    (BinaryFractionalGraphOracle.selected adjacency y ds).1.map
      (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address) := by
  exact value_refines _ payload address _

/-- The very same lower-machine run returns the exact encoding of the existing
graph-selected record. Its original linked list, payload and address survive
in the same heap. Decoding the opaque payload remains a separate interface.
All representation, size and precomputed-path premises remain explicit. -/
theorem selected_bit {n H B M : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (payload address : BinaryFractionalGraphOracle.Selected n → ℕ)
    (initial : BitState 194) (bounded : initial.Bounded H B)
    (pc0 : initial.pc=178) (hn : value initial.next=initial.heap.length)
    (input : ItemList (eraseState initial).heap (eraseState initial).registers.a
      (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map
        (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address)))
    (empty : initial.stack=[])
    (size : ∀ x∈(BinaryFractionalGraphOracle.collect adjacency y ds).1,
      x.path.cost.num.length ≤ M ∧ x.path.cost.den.length ≤ M) :
    let xs := ((BinaryFractionalGraphOracle.collect adjacency y ds).1).map
      (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address)
    ∃ charge out, Run program (steps xs) charge initial [] out ∧
      RetainedArgminProgram.Selected (eraseState out).heap (eraseState out).registers.d
        ((BinaryFractionalGraphOracle.selected adjacency y ds).1.map
          (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address)) ∧
      ItemList (eraseState out).heap (eraseState initial).registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells xs) ∧
      out.Bounded (H+steps xs) (B+steps xs) ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 194 H B
        ((6400*(M+1)^2+12)*(BinaryFractionalGraphOracle.collect adjacency y ds).1.length+5) ∧
      steps xs ≤ (6400*(M+1)^2+12)*(BinaryFractionalGraphOracle.collect adjacency y ds).1.length+5 := by
  dsimp only
  obtain ⟨charge,out,run,selected,retained,source,stack,extension,width,halt,cost⟩ :=
    select_bit _ initial bounded pc0 hn input empty
  rw [selected_refines] at selected
  have hb : steps (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map
      (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address)) ≤
      (6400*(M+1)^2+12)*(BinaryFractionalGraphOracle.collect adjacency y ds).1.length+5 := by
    have h := steps_bound (M:=M) (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map
      (item (fun x : BinaryFractionalGraphOracle.Selected n => (x.path.cost,4)) payload address)) ?_
    · simpa only [List.length_map] using h
    · intro a ha
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      exact size x hx
  exact ⟨charge,out,run,selected,retained,source,stack,extension,width,halt,
    cost.trans (complete_bound_mono H B hb),hb⟩

end DirectedFlowCutGap.RetainedGraphArgmin
