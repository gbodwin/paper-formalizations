import DirectedFlowCutGap.CostedCandidateBounds
import DirectedFlowCutGap.MaterializedGraphPath

/-! Exact graph-selector refinement after actual costed-record construction.
Only the original path/source words and opaque payloads are represented inputs;
the machine computes all cost fields, allocates occurrence-specific records,
and runs stable selection on that same list. Path discovery remains separate. -/
namespace DirectedFlowCutGap.MaterializedGraphSelection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow
open CostedCandidateMaterialization ImmutableReferenceSimulation ImmutableReferenceTerminal

/-- The address is hidden only in the semantic observation; the lower result
continues to retain the actual allocated record address. -/
def observe (x : RetainedArgminProgram.Item) : RetainedArgminProgram.Item :=
  ⟨x.score,x.payload,0⟩

theorem observe_choose (x y : RetainedArgminProgram.Item) :
    observe (RetainedArgminProgram.choose x y)=RetainedArgminProgram.choose (observe x) (observe y) := by
  unfold RetainedArgminProgram.choose RetainedArgminProgram.keep observe
  split <;> rfl

theorem observe_from (xs : List RetainedArgminProgram.Item) (x : RetainedArgminProgram.Item) :
    observe (RetainedArgminProgram.selectFrom x xs)=
      RetainedArgminProgram.selectFrom (observe x) (xs.map observe) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp only [RetainedArgminProgram.selectFrom,List.map_cons,ih,observe_choose]

theorem observe_select (xs : List RetainedArgminProgram.Item) :
    (RetainedArgminProgram.select xs).map observe=RetainedArgminProgram.select (xs.map observe) := by
  cases xs with
  | nil => rfl
  | cons x xs => exact congrArg some (observe_from xs x)

theorem observe_items (rows : List Fraction) (next : ℕ) (xs : List Candidate) :
    (items rows next xs).map observe=
      xs.map (RetainedGraphArgmin.item (fun x => (score rows x,0)) Candidate.payload (fun _ => 0)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [items,observe,RetainedGraphArgmin.item,ih]

theorem candidates_refine (rows : List Fraction) (next : ℕ) (xs : List Candidate) :
    (RetainedArgminProgram.select (items rows next xs)).map observe=
      (BinaryFractionalGraphOracle.argmin (fun x => (score rows x,0)) xs).1.map
        (RetainedGraphArgmin.item (fun x => (score rows x,0)) Candidate.payload (fun _ => 0)) := by
  rw [observe_select,observe_items]
  exact RetainedGraphArgmin.value_refines _ _ _ _

/-- Recovery itself constructs its stored cost from the returned edge list. -/
theorem shortest_cost {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (cost : BinaryFractionalWalkOracle.Cost n)
    (s t : Fin n) {q : BinaryFractionalWalkOracle.Candidate n}
    (hq : (BinaryFractionalWalkOracle.shortest E adjacency cost s t).1=some q) :
    q.cost=(CanonicalPathCost.candidate cost q.edges).cost := by
  unfold BinaryFractionalWalkOracle.shortest at hq
  cases hm : (BinaryFractionalWalkOracle.minimize E adjacency cost s t).1 with
  | none => simp [hm] at hq
  | some p =>
    simp only [hm,Option.some.injEq] at hq
    rw [← hq,CanonicalPathCost.candidate_cost]
    rfl

theorem collected_cost {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    ∀ q∈(BinaryFractionalGraphOracle.collect adjacency y ds).1,
      q.path.cost=(CanonicalPathCost.candidate (BinaryFractionalGraphOracle.outgoing y q.demand.1) q.path.edges).cost := by
  induction ds with
  | nil => simp [BinaryFractionalGraphOracle.collect]
  | cons d ds ih =>
    cases hp : (BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n)
        adjacency (BinaryFractionalGraphOracle.outgoing y d.1) d.1 d.2).1 with
    | none => simpa [BinaryFractionalGraphOracle.collect,hp] using ih
    | some p =>
      intro q hq
      simp only [BinaryFractionalGraphOracle.collect,hp,List.mem_cons] at hq
      rcases hq with rfl|hq
      · exact shortest_cost _ _ _ _ _ hp
      · exact ih q hq

def encode {n : ℕ} (words : BinaryFractionalGraphOracle.Selected n → List Bits)
    (sources : BinaryFractionalGraphOracle.Selected n → Bits)
    (payload : BinaryFractionalGraphOracle.Selected n → ℕ) (q : BinaryFractionalGraphOracle.Selected n) : Candidate :=
  ⟨words q,sources q,payload q⟩

theorem graph_items {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (words : BinaryFractionalGraphOracle.Selected n → List Bits)
    (sources : BinaryFractionalGraphOracle.Selected n → Bits)
    (payload : BinaryFractionalGraphOracle.Selected n → ℕ)
    (encoding : ∀ q∈(BinaryFractionalGraphOracle.collect adjacency y ds).1,
      MaterializedGraphPath.Encodes (words q) q.path.edges ∧ value (sources q)=q.demand.1.val)
    (next : ℕ) :
    (items y.toList next (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload))).map observe=
      ((BinaryFractionalGraphOracle.collect adjacency y ds).1).map
        (RetainedGraphArgmin.item (fun q => (q.path.cost,4)) payload (fun _ => 0)) := by
  rw [observe_items,List.map_map]
  apply List.map_congr_left
  intro q hq
  have hc := MaterializedGraphPath.result_eq y q.demand.1 (sources q) (encoding q hq).2 (encoding q hq).1
  rw [← collected_cost adjacency y ds q hq] at hc
  simp [RetainedGraphArgmin.item,score,encode,hc]

/-- The address-free semantic observation equals the exact old selected record,
including the old first-minimum tie rule and retained payload. -/
theorem graph_refines {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (words : BinaryFractionalGraphOracle.Selected n → List Bits)
    (sources : BinaryFractionalGraphOracle.Selected n → Bits)
    (payload : BinaryFractionalGraphOracle.Selected n → ℕ)
    (encoding : ∀ q∈(BinaryFractionalGraphOracle.collect adjacency y ds).1,
      MaterializedGraphPath.Encodes (words q) q.path.edges ∧ value (sources q)=q.demand.1.val)
    (next : ℕ) :
    (RetainedArgminProgram.select (items y.toList next
      (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload)))).map observe=
      (BinaryFractionalGraphOracle.selected adjacency y ds).1.map
        (RetainedGraphArgmin.item (fun q => (q.path.cost,4)) payload (fun _ => 0)) := by
  rw [observe_select,graph_items adjacency y ds words sources payload encoding]
  exact RetainedGraphArgmin.selected_refines adjacency y ds payload (fun _ => 0)

/-- This actual machine takes uncosted path records, materializes all costs and
selects the original payload. The returned real record address remains visible.
The supplied collection consists of the old discovered paths; discovering and
encoding that collection is a later machine obligation. -/
theorem graph_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (words : BinaryFractionalGraphOracle.Selected n → List Bits)
    (sources : BinaryFractionalGraphOracle.Selected n → Bits)
    (payload : BinaryFractionalGraphOracle.Selected n → ℕ)
    (encoding : ∀ q∈(BinaryFractionalGraphOracle.collect adjacency y ds).1,
      MaterializedGraphPath.Encodes (words q) q.path.edges ∧ value (sources q)=q.demand.1.val)
    (initial : BitState 501) (bounded : initial.Bounded H A) (pc0 : initial.pc=305)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : CandidateList (eraseState initial).heap (eraseState initial).registers.a
      (((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload)))
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (IndexedRationalRead.fields y.toList))
    (M B : ℕ) (hB : 1 ≤ B) (rowWidths : ∀ x∈y.toList,StoredBounded x B)
    (pathBounds : ∀ q∈(BinaryFractionalGraphOracle.collect adjacency y ds).1,
      (words q).length ≤ M ∧ (sources q).length ≤ B ∧ ∀ w∈words q,w.length ≤ B) :
    let xs := ((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload)
    ∃ charge out chosen,Run CostedCandidateSelection.program
        (CostedCandidateSelection.steps y.toList (value initial.next) xs) charge initial [] out ∧
      RetainedArgminProgram.Selected (eraseState out).heap (eraseState out).registers.d chosen ∧
      chosen.map observe=(BinaryFractionalGraphOracle.selected adjacency y ds).1.map
        (RetainedGraphArgmin.item (fun q => (q.path.cost,4)) payload (fun _ => 0)) ∧
      CandidateList (eraseState out).heap (eraseState initial).registers.a xs ∧
      (∃ itemRoot,RetainedArgminProgram.ItemList (eraseState out).heap itemRoot (items y.toList (value initial.next) xs)) ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (attempt CostedCandidateSelection.program out).result=none ∧
      charge+(attempt CostedCandidateSelection.program out).operations ≤
        completeBound 501 H A (CostedCandidateBounds.instructionBound xs.length M B n) := by
  dsimp only
  have valid : ∀ x∈((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload),
      ∀ w∈x.words,value w<y.toList.length := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    simpa [encode] using MaterializedGraphPath.indices_valid (encoding q hq).1
  have sizes : ∀ x∈((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload),
      CostedCandidateBounds.InputBound B M x := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact pathBounds q hq
  have indices : ∀ x∈((BinaryFractionalGraphOracle.collect adjacency y ds).1).map (encode words sources payload),
      ∀ w∈x.words,value w ≤ n := by
    intro x hx w hw
    exact (show value w<n by simpa using valid x hx w hw).le
  obtain ⟨charge,out,run,sel,retained,itemRep,src,stack,_,halt,cost⟩ :=
    CostedCandidateBounds.select_bit_bounded initial bounded pc0 hn empty input table M B n hB rowWidths sizes valid indices
  exact ⟨charge,out,_,run,sel,graph_refines adjacency y ds words sources payload encoding _,
    retained,itemRep,src,stack,halt,cost⟩

end DirectedFlowCutGap.MaterializedGraphSelection
