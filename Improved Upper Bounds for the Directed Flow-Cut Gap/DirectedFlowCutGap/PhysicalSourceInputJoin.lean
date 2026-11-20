import DirectedFlowCutGap.OriginalSourceFramingRefinement
import DirectedFlowCutGap.OriginalSourceTableReadback
import DirectedFlowCutGap.ChargedSourceAssembly
import DirectedFlowCutGap.PackedArrayReservations

/-! Join the original typed decoders to the bit-addressed framing and
readback. Every table field is read from the retained physical heap. -/
namespace DirectedFlowCutGap.PhysicalSourceInputJoin

open BinaryArithmetic ImmutableReferenceSimulation PhysicalCoverAccess
open EncodedVertexInput (Table)
open OriginalSourceTableReadback (table table_value table_paid tableBudget)

private theorem bind_value {A B : Type} (r : Read A) (k : A → Read B) :
    (Read.bind r k).1=r.1.bind (fun a => (k a).1) := Read.bind_value r k

private def retained (s : BitState 64) : Read (Table × Table × Table × Bits) := do
  let costs ← table s.heap s.registers.a
  let matrix ← table s.heap s.registers.b
  let demands ← table s.heap s.registers.d
  pure (costs,matrix,demands,s.source)

def tables (source : Bits) : Read (Table × Table × Table × Bits) :=
  let phase := Read.bind (OriginalSourceFraming.readBinary source) retained
  (phase.1,phase.2+8)

theorem tables_value (source : Bits) : (tables source).1=EncodedVertexInput.readTables source := by
  have frames := (OriginalSourceFraming.readBinary_checked source).1
  cases parsed : EncodedVertexInput.readTables source with
  | none =>
      have rejected := frames.trans ((OriginalSourceFraming.original_none source).mpr parsed)
      simp only [tables,bind_value,rejected,Option.bind_none]
  | some data =>
      obtain ⟨c,m,d,suffix⟩ := data
      obtain ⟨s,ran,hs,hc,hm,hd,_,_,_⟩ := OriginalSourceFraming.original_tables parsed
      have found := frames.trans ran
      have costs : (table s.heap s.registers.a).1=some c := table_value hc
      have matrix : (table s.heap s.registers.b).1=some m := table_value hm
      have demands : (table s.heap s.registers.d).1=some d := table_value hd
      simp only [tables,bind_value,found,Option.bind_some,retained,Read.bind_value,
        costs,matrix,demands,Read.pure_value,hs]

def framingBudget {R : Type*} [Semiring R] (x : R) : R :=
  let fuel := 8*(x+6)+1
  539136*(x+7)^3+80+(fuel+1)*(64*(2*fuel+3))+16*(x+1)^2+32*(x+10)+17*(fuel+1)+24

def tablesBudget {R : Type*} [Semiring R] (x : R) : R :=
  framingBudget x+3*tableBudget (1+8*(x+6)) (8*(x+6))+8

private theorem tableBudget_mono {H H' B : ℕ} (steps : H≤H') : tableBudget H B≤tableBudget H' B := by
  unfold tableBudget
  dsimp only
  gcongr

theorem tables_paid (source : Bits) : (tables source).2≤tablesBudget source.length := by
  let width := 8*(source.length+6)
  let cost := tableBudget (1+width) width
  have framed := (OriginalSourceFraming.readBinary_checked source).2
  have phase : (Read.bind (OriginalSourceFraming.readBinary source) retained).2≤framingBudget source.length+3*cost := by
    apply Read.bind_bound framed
    intro s ran
    have accepted := (OriginalSourceFraming.readBinary_checked source).1.symm.trans ran
    have bound := OriginalSourceFraming.read_bounded accepted
    have cells : s.heap.length≤1+width := by
      have total := bound.1
      unfold State.records at total
      exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans total)
    let fit := bound.2.2.2.1
    let heap := bound.2.2.1
    have costs : (table s.heap s.registers.a).2≤cost := (table_paid heap fit.1).trans (tableBudget_mono cells)
    have matrix : (table s.heap s.registers.b).2≤cost := (table_paid heap fit.2.1).trans (tableBudget_mono cells)
    have demands : (table s.heap s.registers.d).2≤cost := (table_paid heap fit.2.2.2).trans (tableBudget_mono cells)
    have whole : (retained s).2≤cost+(cost+(cost+0)) := by
      unfold retained
      apply Read.bind_bound costs
      intro _ _
      apply Read.bind_bound matrix
      intro _ _
      apply Read.bind_bound demands
      intro _ _
      exact Nat.le_refl 0
    exact whole.trans (by omega)
  exact Nat.add_le_add_right phase 8

private def finish {A : Type} (assemble : Table → Table → Table → Read A) :
    Table × Table × Table × Bits → Read A
  | (costs,matrix,demands,suffix) =>
      if suffix.isEmpty then assemble costs matrix demands else Read.failure

private def assembleInput {A : Type} (assemble : Table → Table → Table → Read A) (source : Bits) : Read A :=
  let result := Read.bind (tables source) (finish assemble)
  (result.1,result.2+5)

def vertex (source : Bits) : Read EncodedVertexInput.Input :=
  assembleInput ChargedSourceAssembly.vertexAssembly source

def edge (source : Bits) : Read (Σ n,EncodedEdgeInput.Input n) :=
  assembleInput ChargedSourceAssembly.edgeAssembly source

theorem vertex_value (source : Bits) : (vertex source).1=EncodedVertexInput.parse source := by
  simp only [vertex,assembleInput,bind_value,tables_value,EncodedVertexInput.parse]
  congr 1
  funext fields
  obtain ⟨c,m,d,suffix⟩ := fields
  by_cases empty : suffix.isEmpty=true <;> simp [finish,empty,Read.failure,ChargedSourceAssembly.vertexAssembly_value]

theorem edge_value (source : Bits) : (edge source).1=EncodedEdgeInput.parse source := by
  simp only [edge,assembleInput,bind_value,tables_value,EncodedEdgeInput.parse]
  congr 1
  funext fields
  obtain ⟨c,m,d,suffix⟩ := fields
  by_cases empty : suffix.isEmpty=true <;> simp [finish,empty,Read.failure,ChargedSourceAssembly.edgeAssembly_value]

private theorem replacement_paid {A : Type} (assemble : Table → Table → Table → Read A) (source : Bits)
    (bound : (Read.bind (ChargedSourceTables.tables source) (finish assemble)).2+5≤
      ChargedSourceAssembly.parseBudget source.length) :
    (assembleInput assemble source).2≤tablesBudget source.length+ChargedSourceAssembly.parseBudget source.length := by
  have eq := (tables_value source).trans (ChargedSourceTables.tables_value source).symm
  have measured := tables_paid source
  unfold assembleInput
  cases parsed : (tables source).1 with
  | none =>
      simp only [Read.bind,parsed]
      have fuel : 5≤ChargedSourceAssembly.parseBudget source.length := by unfold ChargedSourceAssembly.parseBudget; omega
      omega
  | some data =>
      have old : (ChargedSourceTables.tables source).1=some data := eq.symm.trans parsed
      simp only [Read.bind,parsed,old] at bound ⊢
      omega

theorem vertex_paid (source : Bits) :
    (vertex source).2≤tablesBudget source.length+ChargedSourceAssembly.parseBudget source.length :=
  replacement_paid _ _ (ChargedSourceAssembly.vertex_paid source)

theorem edge_paid (source : Bits) :
    (edge source).2≤tablesBudget source.length+ChargedSourceAssembly.parseBudget source.length :=
  replacement_paid _ _ (ChargedSourceAssembly.edge_paid source)

open Polynomial in
noncomputable def parsePolynomial : Polynomial ℕ :=
  tablesBudget X+ChargedSourceAssembly.parsePolynomial

open Polynomial in
theorem parsePolynomial_eval (x : ℕ) :
    parsePolynomial.eval x=tablesBudget x+ChargedSourceAssembly.parseBudget x := by
  simp only [parsePolynomial,tablesBudget,framingBudget,tableBudget,eval_add,eval_mul,eval_pow,
    eval_ofNat,eval_X,eval_one,ChargedSourceAssembly.parsePolynomial_eval]

section Arrays

open EncodedArrayStorage (Instruction fresh allocateTrace)
open ChargedSourceAssembly (copyBudget allocationBudget)

private def inputArrayCode (assembly : Table → Table → Table → List (Instruction Unit))
    (source : Bits) : List (Instruction Unit) :=
  match (tables source).1 with
  | none => []
  | some (C,M,D,suffix) => if suffix.isEmpty then assembly C M D else []

def vertexArrayCode : Bits → List (Instruction Unit) := inputArrayCode ChargedSourceAssembly.vertexArrayCode
def edgeArrayCode : Bits → List (Instruction Unit) := inputArrayCode ChargedSourceAssembly.edgeArrayCode

private theorem row_counts {source suffix : Bits} {C M D : Table}
    (read : (tables source).1 = some (C,M,D,suffix)) :
    C.length ≤ source.length ∧ M.length ≤ source.length := by
  have old : (ChargedSourceTables.tables source).1=some (C,M,D,suffix) :=
    ((ChargedSourceTables.tables_value source).trans (tables_value source).symm).trans read
  have wire := congrArg List.length (ChargedSourceTables.tables_wire old)
  simp only [PackingSourceInput.encode,List.length_append] at wire
  have prices := EncodedVertexInput.table_prefix_has_fuel C []
  have rows := EncodedVertexInput.table_prefix_has_fuel M []
  simp only [List.append_nil] at prices rows
  omega

private theorem input_array_counts (assembly : Table → Table → Table → List (Instruction Unit))
    (bounded : ∀ {C M D : Table} {width : ℕ}, C.length ≤ width → M.length ≤ width →
      (assembly C M D).length ≤ copyBudget width ∧ fresh (assembly C M D) ≤ allocationBudget width)
    (source : Bits) :
    (inputArrayCode assembly source).length ≤ copyBudget source.length ∧
      fresh (inputArrayCode assembly source) ≤ allocationBudget source.length := by
  unfold inputArrayCode
  cases read : (tables source).1 with
  | none => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | some retained =>
      obtain ⟨C,M,D,suffix⟩ := retained
      obtain ⟨costs,rows⟩ := row_counts read
      simp only
      split
      · exact bounded costs rows
      · exact ⟨Nat.zero_le _,Nat.zero_le _⟩

theorem vertex_array_counts (source : Bits) :
    (vertexArrayCode source).length ≤ copyBudget source.length ∧
      fresh (vertexArrayCode source) ≤ allocationBudget source.length :=
  input_array_counts _ ChargedSourceAssembly.vertex_array_paid source

theorem edge_array_counts (source : Bits) :
    (edgeArrayCode source).length ≤ copyBudget source.length ∧
      fresh (edgeArrayCode source) ≤ allocationBudget source.length :=
  input_array_counts _ ChargedSourceAssembly.edge_array_paid source

private theorem array_layout (source : Bits) (code : List (Instruction Unit)) (start : ℕ)
    (bounds : code.length ≤ copyBudget source.length ∧ fresh code ≤ allocationBudget source.length) :
    let placed := allocateTrace start code
    let width := (start+allocationBudget source.length).size
    let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
    (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
      binary.charge ≤ BinaryAllocationTrace.chargeBound (copyBudget source.length) width ∧
      ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
  have fits : (start+fresh code).size ≤ (start+allocationBudget source.length).size :=
    Nat.size_le_size (Nat.add_le_add_left bounds.2 start)
  refine ⟨same,paid.trans ?_, fun block member offset inside => (widths block member offset inside).trans fits⟩
  unfold BinaryAllocationTrace.chargeBound
  have copies := bounds.1
  gcongr

/-- Model the reached typed vector constructors and their reservations on any literal vertex source. -/
theorem vertex_arrays (source : Bits) (start : ℕ) :
    let code := vertexArrayCode source
    let placed := allocateTrace start code
    let width := (start+allocationBudget source.length).size
    let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
    (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
      binary.charge ≤ BinaryAllocationTrace.chargeBound (copyBudget source.length) width ∧
      ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width :=
  array_layout source (vertexArrayCode source) start (vertex_array_counts source)

/-- Model the reached typed vector constructors and their reservations on any literal edge source. -/
theorem edge_arrays (source : Bits) (start : ℕ) :
    let code := edgeArrayCode source
    let placed := allocateTrace start code
    let width := (start+allocationBudget source.length).size
    let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
    (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
      binary.charge ≤ BinaryAllocationTrace.chargeBound (copyBudget source.length) width ∧
      ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width :=
  array_layout source (edgeArrayCode source) start (edge_array_counts source)

end Arrays

end DirectedFlowCutGap.PhysicalSourceInputJoin
