import DirectedFlowCutGap.ActualCompletePacking

namespace DirectedFlowCutGap.PackingInput
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation
open PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

def program : Program 6 := fun pc => match pc.val with
  | 0 => .make .r0 (.pair .r1 .r0) 1
  | 1 => .make .r2 (.pair .r2 .r0) 2
  | 2 => .make .r2 (.pair .r1 .r2) 3
  | 3 => .make .r3 (.pair .r3 .r2) 4
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 6) : NaturalState 6 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

theorem capacity_fields {n : ℕ} (capacity : Row n) :
    IndexedRationalRead.fields capacity.toList=
      (List.finRange n).map (fun i => ((get capacity i).num,(get capacity i).den)) := by
  apply List.ext_getElem
  · simp [IndexedRationalRead.fields]
  · intro i hi hj
    simp [IndexedRationalRead.fields,BinaryFractionalRows.get]

/-- Four actual allocations build all composite packing metadata from the same
primitive capacity, vertex, adjacency and demand lists. -/
theorem construct {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits) (xs : List DemandCollection.Demand)
    {heap : NaturalHeap} {cap vertices matrix demands : ℕ}
    (caps : StoredList heap cap capacity.toList)
    (verts : GraphDiscoveryProgram.Vertices heap vertices ((List.finRange n).map label))
    (graph : GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap demands xs)
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ ext,ext.length=4 ∧
      NaturalRun program 4 (state heap next cap vertices matrix demands source 0) []
        (state (heap++ext) (next+4) next vertices (next+2) (next+3) source 4) ∧
      PackingStart.Input (heap++ext) (next+3) label adjacency capacity xs := by
  let e1 : NaturalHeap := [.pair vertices cap]
  let e2 : NaturalHeap := e1++[.pair matrix next]
  let e3 : NaturalHeap := e2++[.pair vertices (next+1)]
  let ext : NaturalHeap := e3++[.pair demands (next+2)]
  have t0 : tickNatural program (state heap next cap vertices matrix demands source 0)=
      some ⟨state (heap++e1) (next+1) next vertices matrix demands source 1,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,e1]
  have t1 : tickNatural program (state (heap++e1) (next+1) next vertices matrix demands source 1)=
      some ⟨state (heap++e2) (next+2) next vertices (next+1) demands source 2,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,e2,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state (heap++e2) (next+2) next vertices (next+1) demands source 2)=
      some ⟨state (heap++e3) (next+3) next vertices (next+2) demands source 3,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,e3,List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program (state (heap++e3) (next+3) next vertices (next+2) demands source 3)=
      some ⟨state (heap++ext) (next+4) next vertices (next+2) (next+3) source 4,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext,List.append_assoc,Nat.add_assoc]
  refine ⟨ext,by simp [ext,e3,e2,e1],.step t0 (.step t1 (.step t2 (.step t3 (.done _)))),?_⟩
  have post : CapacityBottleneck.GraphContext (heap++ext) next label capacity := by
    refine ⟨vertices,cap,?_,GraphDiscoveryProgram.vertices_extend verts ext,?_⟩
    · simp [ext,e3,e2,e1,dense]
    · have h := PackingGraphContext.row_table (list_extend caps ext)
      simpa only [capacity_fields] using h
  refine ⟨demands,next+2,?_,DemandCollection.demands_extend pairs ext,vertices,next+1,matrix,next,?_,?_,?_,GraphAdjacencyProgram.matrix_extend graph ext,post⟩
  · simp [ext,e3,e2,e1,dense]
  · simp [ext,e3,e2,e1,dense]
  · simp [ext,e3,e2,e1,dense]
  · simpa [IntegralNetworkFlow.ResidualSearch.Enumeration.fin,IntegralNetworkFlow.ResidualSearch.Enumeration.ofEquiv,List.finRange,List.map_ofFn,Function.comp_def] using GraphDiscoveryProgram.vertices_extend verts ext
end DirectedFlowCutGap.PackingInput
