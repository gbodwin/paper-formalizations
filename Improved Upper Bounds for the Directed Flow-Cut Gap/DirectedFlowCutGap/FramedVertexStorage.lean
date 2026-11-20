import DirectedFlowCutGap.PaidFramedVertexCost
import DirectedFlowCutGap.VertexSourceTerminalLayout

/-! Place the typed input arrays before the completed cache and returned arrays
of the vertex fractional source. Rejected sources keep the input prefix. -/
namespace DirectedFlowCutGap.FramedVertexStorage

open BinaryArithmetic Polynomial
open EncodedArrayStorage (Instruction fresh fresh_append allocateTrace)
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalSourceDispatch (initial program)
open CachedReferenceExecution (FastState)
open PaidFramedVertexWire (serializedLengthBound serialized_length_le)

theorem array_polynomial : ∃ cells copies : Polynomial ℕ, ∀ source : Bits,
    let pre := PhysicalSourceInputJoin.vertexArrayCode source
    ∃ post : List (Instruction Unit),
      (match (PhysicalSourceInputJoin.vertex source).1 with
       | none => post=[]
       | some ⟨_, D⟩ =>
          let bits := (BinarySourceSerialization.run D).1
          let out := (PhysicalSourceBinaryCache.evaluate D bits (BinarySourceSerialization.run_value D)).1.1
          let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
          ∃ cache : List (Instruction Unit),
            post = cache ++ BinaryCoverReadback.terminalArrayCode plan ∧
            (PhysicalSourceReadback.runWithBitCharges D).1.1 = some plan ∧
            ∀ start : ℕ,
              let first := allocateTrace start pre
              let placed := allocateTrace first.1 cache
              PaidCacheTrace.Layout program (FastState.ofReference (initial bits)) first.1 out placed.1 placed.2) ∧
      let code := pre ++ post
      fresh code ≤ cells.eval source.length ∧ code.length ≤ copies.eval source.length ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval source.length).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b))) = placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval source.length) width ∧
          ∀ block ∈ placed.2, ∀ offset < block.2, (block.1+offset).size ≤ width := by
  obtain ⟨sourceCells,sourceCopies,sourceLayout⟩ := VertexSourceTerminalLayout.array_polynomial
  let inputCells : Polynomial ℕ := (X+2)*(X^2+7*X+2)
  let inputCopies : Polynomial ℕ := (X+2)*(2*X^2+21*X+4)
  let cells := inputCells+sourceCells.comp serializedLengthBound
  let copies := inputCopies+sourceCopies.comp serializedLengthBound
  refine ⟨cells,copies,?_⟩
  intro source
  let pre := PhysicalSourceInputJoin.vertexArrayCode source
  have inputBounds := PhysicalSourceInputJoin.vertex_array_counts source
  have inputSpace : fresh pre ≤ inputCells.eval source.length := by
    simp only [inputCells,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
    exact inputBounds.2
  have inputWork : pre.length ≤ inputCopies.eval source.length := by
    simp only [inputCopies,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
    exact inputBounds.1
  have finish (post : List (Instruction Unit))
      (postSpace : fresh post ≤ sourceCells.eval (serializedLengthBound.eval source.length))
      (postWork : post.length ≤ sourceCopies.eval (serializedLengthBound.eval source.length)) :
      let code := pre ++ post
      fresh code ≤ cells.eval source.length ∧ code.length ≤ copies.eval source.length ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval source.length).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b))) = placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval source.length) width ∧
          ∀ block ∈ placed.2, ∀ offset < block.2, (block.1+offset).size ≤ width := by
    let code := pre ++ post
    have space : fresh code ≤ cells.eval source.length := by
      simpa only [code,fresh_append,cells,eval_add,eval_comp] using Nat.add_le_add inputSpace postSpace
    have work : code.length ≤ copies.eval source.length := by
      simpa only [code,List.length_append,copies,eval_add,eval_comp] using Nat.add_le_add inputWork postWork
    refine ⟨space,work,fun start => ?_⟩
    obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
    have fits : (start+fresh code).size ≤ (start+cells.eval source.length).size :=
      Nat.size_le_size (Nat.add_le_add_left space start)
    exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
      fun block member offset inside => (widths block member offset inside).trans fits⟩
  cases parsed : (PhysicalSourceInputJoin.vertex source).1 with
  | none => exact ⟨[],rfl,finish [] (Nat.zero_le _) (Nat.zero_le _)⟩
  | some accepted =>
    obtain ⟨n,D⟩ := accepted
    have width : (BinarySourceSerialization.run D).1.length ≤ serializedLengthBound.eval source.length := by
      rw [BinarySourceSerialization.run_value]
      exact serialized_length_le parsed
    obtain ⟨cache,returned,space,work,placed⟩ := sourceLayout D
    refine ⟨_,⟨cache,rfl,returned,fun start => (placed (allocateTrace start pre).1).1⟩,?_⟩
    exact finish _ (space.trans (eval_mono _ width)) (work.trans (eval_mono _ width))

end DirectedFlowCutGap.FramedVertexStorage
