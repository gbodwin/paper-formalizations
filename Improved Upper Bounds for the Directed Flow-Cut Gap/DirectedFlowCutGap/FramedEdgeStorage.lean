import DirectedFlowCutGap.PhysicalLineStorage
import DirectedFlowCutGap.PaidFramedEdgeCost
import DirectedFlowCutGap.VertexSourceTerminalLayout

/-! The accepted edge source reserves its decoded price and line arrays
before the cache and returned-plan arrays. Rejection keeps the input prefix. -/
namespace DirectedFlowCutGap.FramedEdgeStorage

open BinaryArithmetic Polynomial EncodedArrayStorage
open BinaryArrayNestedStorage (Code Grid cellBudget cellBudget_eval cellBudget_mono
  copyBudget copyBudget_eval copyBudget_mono)
open CachedReferenceExecution (FastState)
open PhysicalIntegerRoundingCost (eval_mono)
open EncodedEdgeLineInput (lineSize)

def AfterInput {n : ℕ} (D : EncodedEdgeInput.Input n) (pre post : Code) : Prop :=
  let prices := (PhysicalBinaryEdgeWire.decodeWithCost D).1
  let line := (PhysicalAmplifiedBinaryEdge.lineWithCost prices).1
  let source := (BinarySourceSerialization.run line).1
  let out := (PhysicalSourceBinaryCache.evaluate line source (BinarySourceSerialization.run_value line)).1.1
  let returned := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput line).1
  ∃ priceCode lineCode cache : Code,
    Grid prices.costs priceCode ∧ PhysicalLineStorage.LineArrays prices lineCode ∧
    post=priceCode++lineCode++(cache++BinaryCoverReadback.terminalArrayCode returned) ∧
    ((PhysicalSourceReadback.runWithTerminalCharge line).1.map Prod.fst)=some returned ∧
    ∀ start : ℕ,
      let previous := allocateTrace start (pre++priceCode++lineCode)
      let placed := allocateTrace previous.1 cache
      PaidCacheTrace.Layout PhysicalSourceDispatch.program (FastState.ofReference (PhysicalSourceDispatch.initial source))
        previous.1 out placed.1 placed.2

/-- Addresses are relative to the existing heap extent `start`. The modeled
array allocation and copy counts are polynomial in the original source length. -/
theorem array_polynomial : ∃ cells copies : Polynomial ℕ, ∀ source : Bits,
    let pre := PhysicalSourceInputJoin.edgeArrayCode source
    ∃ post : Code,
      (match (PhysicalSourceInputJoin.edge source).1 with
      | none => post=[]
      | some ⟨_,D⟩ => AfterInput D pre post) ∧
      let code := pre++post
      fresh code ≤ cells.eval source.length ∧ code.length ≤ copies.eval source.length ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval source.length).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval source.length) width ∧
          ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
  obtain ⟨terminalCells,terminalCopies,terminal⟩ := VertexSourceTerminalLayout.array_polynomial
  obtain ⟨serialized,serializedBound⟩ := PaidDirectEdgeWire.serialized_line_length
  let dimension : Polynomial ℕ := X*2+X*X
  let inputCells : Polynomial ℕ := (X+2)*(X^2+7*X+2)
  let inputCopies : Polynomial ℕ := (X+2)*(2*X^2+21*X+4)
  let priceCells : Polynomial ℕ := (X+1)*cellBudget X
  let priceCopies : Polynomial ℕ := (X+1)*copyBudget X
  let lineCells := (dimension+4)*cellBudget dimension
  let lineCopies := (dimension+4)*copyBudget dimension
  let laterCells := priceCells+lineCells+terminalCells.comp serialized
  let laterCopies := priceCopies+lineCopies+terminalCopies.comp serialized
  let cells := inputCells+laterCells
  let copies := inputCopies+laterCopies
  refine ⟨cells,copies,?_⟩
  intro source
  let x := source.length
  let pre := PhysicalSourceInputJoin.edgeArrayCode source
  have inputBounds := PhysicalSourceInputJoin.edge_array_counts source
  have inputSpace : fresh pre ≤ inputCells.eval x := by
    simp only [inputCells,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
    exact inputBounds.2
  have inputWork : pre.length ≤ inputCopies.eval x := by
    simp only [inputCopies,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
    exact inputBounds.1
  have finish (post : Code) (space : fresh post ≤ laterCells.eval x) (work : post.length ≤ laterCopies.eval x) :
      let code := pre++post
      fresh code ≤ cells.eval x ∧ code.length ≤ copies.eval x ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval x).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval x) width ∧
          ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
    let code := pre++post
    have hs : fresh code ≤ cells.eval x := by
      simpa only [code,fresh_append,cells,eval_add] using Nat.add_le_add inputSpace space
    have hw : code.length ≤ copies.eval x := by
      simpa only [code,List.length_append,copies,eval_add] using Nat.add_le_add inputWork work
    refine ⟨hs,hw,fun start => ?_⟩
    obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
    have fits : (start+fresh code).size ≤ (start+cells.eval x).size :=
      Nat.size_le_size (Nat.add_le_add_left hs start)
    exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
      fun block member offset inside => (widths block member offset inside).trans fits⟩
  cases parsed : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact ⟨[],rfl,finish [] (by simp [fresh]) (Nat.zero_le _)⟩
  | some decoded =>
    obtain ⟨n,D⟩ := decoded
    let prices := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    let line := (PhysicalAmplifiedBinaryEdge.lineWithCost prices).1
    let returned := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput line).1
    have stored : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
      rwa [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value]
    have hn : n ≤ x := (ChargedSourceAssembly.edge_dimensions stored).1
    have hm : lineSize n ≤ dimension.eval x := by
      simp only [lineSize,dimension,eval_add,eval_mul,eval_ofNat,eval_X]
      gcongr
    obtain ⟨priceCode,priceRun,pw,ps⟩ := PhysicalLineStorage.decode_arrays D
    obtain ⟨lineCode,lineRun,lw,ls⟩ := PhysicalLineStorage.line_arrays prices
    obtain ⟨cache,_,ts,tw,placed⟩ := terminal line
    let post := priceCode++lineCode++(cache++BinaryCoverReadback.terminalArrayCode returned)
    have priceSpace : fresh priceCode ≤ priceCells.eval x := by
      simp only [priceCells,eval_mul,eval_add,eval_one,eval_X,cellBudget_eval]
      exact ps.trans (Nat.mul_le_mul (Nat.add_le_add_right hn 1) (cellBudget_mono hn))
    have priceWork : priceCode.length ≤ priceCopies.eval x := by
      simp only [priceCopies,eval_mul,eval_add,eval_one,eval_X,copyBudget_eval]
      exact pw.trans (Nat.mul_le_mul (Nat.add_le_add_right hn 1) (copyBudget_mono hn))
    have lineSpace : fresh lineCode ≤ lineCells.eval x := by
      simp only [lineCells,eval_mul,eval_add,eval_ofNat,cellBudget_eval]
      exact ls.trans (Nat.mul_le_mul (Nat.add_le_add_right hm 4) (cellBudget_mono hm))
    have lineWork : lineCode.length ≤ lineCopies.eval x := by
      simp only [lineCopies,eval_mul,eval_add,eval_ofNat,copyBudget_eval]
      exact lw.trans (Nat.mul_le_mul (Nat.add_le_add_right hm 4) (copyBudget_mono hm))
    have length := serializedBound parsed
    have terminalSpace : fresh (cache++BinaryCoverReadback.terminalArrayCode returned)≤
        (terminalCells.comp serialized).eval x := by
      rw [eval_comp]
      exact ts.trans (eval_mono _ length)
    have terminalWork : (cache++BinaryCoverReadback.terminalArrayCode returned).length≤
        (terminalCopies.comp serialized).eval x := by
      rw [eval_comp]
      exact tw.trans (eval_mono _ length)
    have extent : fresh post ≤ laterCells.eval x := by
      simpa only [post,fresh_append,laterCells,eval_add] using
        Nat.add_le_add (Nat.add_le_add priceSpace lineSpace) terminalSpace
    have events : post.length ≤ laterCopies.eval x := by
      simpa only [post,List.length_append,laterCopies,eval_add] using
        Nat.add_le_add (Nat.add_le_add priceWork lineWork) terminalWork
    refine ⟨post,⟨priceCode,lineCode,cache,priceRun,lineRun,rfl,?_,fun start => (placed _).1⟩,finish _ extent events⟩
    obtain ⟨dispatch,_,reader,_,observed,_⟩ := PhysicalSourceReadback.terminal_headers line
    rw [observed]
    rfl

end DirectedFlowCutGap.FramedEdgeStorage
