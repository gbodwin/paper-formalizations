import DirectedFlowCutGap.GraphRelaxationExecution
import DirectedFlowCutGap.MaterializedGraphPath

/-! The machine scan refines the frozen graph recurrence with its exact padded
rational fields, chosen edge list, source-zero cost and first-minimum ties. -/
namespace DirectedFlowCutGap.GraphRelaxationRefinement
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension
open GraphRelaxationProgram


def matrix {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) : List Bits :=
  adjacency.toList.map (fun row => row.toList)
def encode {n : ℕ} (label : Fin n → Bits) (q : BinaryFractionalWalkOracle.Candidate n) : Walk :=
  ⟨q.edges.map (fun e => (label e.1,label e.2)),q.cost⟩
def encodeTable {n : ℕ} (label : Fin n → Bits) (xs : BinaryFractionalWalkOracle.Table n) : List Entry :=
  xs.map (fun x => (label x.1,encode label x.2))

theorem matrix_length {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) :
    (matrix adjacency).length=n := by simp [matrix]
theorem matrix_row_length {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (u : Fin n) : ((matrix adjacency)[u.val]'(by simp [matrix,u.isLt])).length=n := by
  simp [matrix]
theorem adjacent_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u v : Fin n) :
    GraphRelaxationProgram.adjacent (matrix adjacency) (label u) (label v)=
      (BinaryFractionalWalkOracle.adjacent adjacency u v).1 := by
  simp [GraphRelaxationProgram.adjacent,matrix,hlabel,BinaryFractionalWalkOracle.adjacent,
    EncodedArrayStorage.readCallback]

theorem extension_eq {n : ℕ} (y : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u v : Fin n)
    (q : BinaryFractionalWalkOracle.Candidate n) :
    GraphWalkExtension.result y.toList sw (label u,label v) (encode label q)=
      encode label (BinaryFractionalWalkOracle.extend (BinaryFractionalGraphOracle.outgoing y s) u v q).1 := by
  simp only [GraphWalkExtension.result,encode,BinaryFractionalWalkOracle.extend,List.map_cons]
  rw [MaterializedGraphPath.outgoing_eq y s (u,v) sw (label u) hs (hlabel u)]

theorem pick_eq {n : ℕ} (label : Fin n → Bits) (q : BinaryFractionalWalkOracle.Candidate n)
    (tail : Option (BinaryFractionalWalkOracle.Candidate n)) :
    GraphRelaxationProgram.pick (encode label q) (tail.map (encode label))=
      ((BinaryFractionalWalkOracle.pick (some q) tail).1).map (encode label) := by
  cases tail with
  | none => rfl
  | some p =>
    change some (if (BinaryRational.le q.cost p.cost).1 then encode label q else encode label p)=
      (if (BinaryRational.le q.cost p.cost).1 then some q else some p).map (encode label)
    cases (BinaryRational.le q.cost p.cost).1 <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,Option.map_some]

theorem scan_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u : Fin n)
    (xs : BinaryFractionalWalkOracle.Table n) :
    GraphRelaxationProgram.scan (matrix adjacency) y.toList sw (label u) (encodeTable label xs)=
      (BinaryFractionalWalkOracle.scan adjacency (BinaryFractionalGraphOracle.outgoing y s) u xs).1.map
        (encode label) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨v,q⟩
    simp only [encodeTable,List.map_cons,GraphRelaxationProgram.scan,BinaryFractionalWalkOracle.scan]
    rw [adjacent_eq adjacency label hlabel u v]
    split
    · rw [show GraphRelaxationProgram.scan (matrix adjacency) y.toList sw (label u)
        (List.map (fun x => (label x.1,encode label x.2)) xs)=_ from ih]
      rw [extension_eq y s sw hs label hlabel u v q,pick_eq]
    · exact ih

/-- The returned old walk and its exact fraction are computed by this one
lower-machine run. Earlier relaxation tables and their representation remain
explicit inputs; bounded rounds, recovery and whole-controller execution are
separate obligations. -/
theorem graph_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u : Fin n)
    (xs : BinaryFractionalWalkOracle.Table n) (initial : ImmutableReferenceSimulation.BitState 532)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=530)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : GraphRelaxationProgram.Table (ImmutableReferenceSimulation.eraseState initial).heap
      (ImmutableReferenceSimulation.eraseState initial).registers.a (encodeTable label xs))
    (context : GraphRelaxationProgram.Context (ImmutableReferenceSimulation.eraseState initial).heap
      (ImmutableReferenceSimulation.eraseState initial).registers.b (matrix adjacency) y.toList (label u) sw)
    (B : ℕ) (hB : 1 ≤ B) (hr : ∀ q∈y.toList,StoredBounded q B)
    (labels : ∀ i,(label i).length ≤ B) (costs : ∀ x∈xs,StoredBounded x.2.cost B) :
    ∃ charge out,ImmutableReferenceSimulation.Run GraphRelaxationProgram.program
      (GraphRelaxationProgram.steps (matrix adjacency) y.toList sw (label u) (encodeTable label xs)+1)
      charge initial [] out ∧
      GraphRelaxationProgram.StoredOption (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState out).registers.d
        ((BinaryFractionalWalkOracle.scan adjacency (BinaryFractionalGraphOracle.outgoing y s) u xs).1.map (encode label)) ∧
      GraphRelaxationProgram.Table (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState initial).registers.a (encodeTable label xs) ∧
      GraphRelaxationProgram.Context (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState initial).registers.b (matrix adjacency) y.toList (label u) sw ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=531 ∧
      (∃ ext,(ImmutableReferenceSimulation.eraseState out).heap=(ImmutableReferenceSimulation.eraseState initial).heap++ext ∧
        ext.length=GraphRelaxationProgram.cells (matrix adjacency) y.toList sw (label u) (encodeTable label xs)) ∧
      (ImmutableReferenceTerminal.attempt GraphRelaxationProgram.program out).result=none ∧
      charge+(ImmutableReferenceTerminal.attempt GraphRelaxationProgram.program out).operations ≤
        ImmutableReferenceTerminal.completeBound 532 H A (GraphRelaxationProgram.instructionBound xs.length B n sw.length) := by
  have hi : value (label u)<(matrix adjacency).length := by simp [hlabel,matrix]
  have hc : value (label u)<y.toList.length := by simp [hlabel]
  have hcols : ∀ x∈encodeTable label xs,value x.1<((matrix adjacency)[value (label u)]).length := by
    intro x hx
    obtain ⟨⟨v,q⟩,_,rfl⟩ := List.mem_map.mp hx
    simp [hlabel,matrix]
  have hxs : ∀ x∈encodeTable label xs,GraphRelaxationProgram.EntryBound B n x := by
    intro x hx
    obtain ⟨⟨v,q⟩,hv,rfl⟩ := List.mem_map.mp hx
    exact ⟨labels v,by simp [hlabel],costs (v,q) hv⟩
  have result := GraphRelaxationProgram.scan_bit initial bounded pc0 hn empty input context hi hc hcols
    B n hB hr (labels u) (by simp [hlabel]) hxs
  rw [scan_eq adjacency y s sw hs label hlabel u xs] at result
  simpa only [encodeTable,List.length_map] using result

end DirectedFlowCutGap.GraphRelaxationRefinement
