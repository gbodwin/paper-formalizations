import DirectedFlowCutGap.AdaptiveRoundRefreshProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private abbrev Store := PackedWordPairTable.Prepared
private abbrev allocate := PackedWordPairTable.allocate
private abbrev word := PackedWordPairTable.word

private def storeList {α : Type} (item : α→Store→Store) : List α→Store→Store
  | [], s => allocate .nil s
  | x::xs, s =>
    let tail := storeList item xs s
    let head := item x tail
    allocate (.pair head.root tail.root) head

private def labelPair (p : Pair 2) (s : Store) : Store :=
  let a := word p.1.val.bits s
  let b := word p.2.val.bits a
  allocate (.pair a.root b.root) b

private def pair (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) :=
  match heap[root]? with
  | some (.pair a b) => some (a,b)
  | _ => none

private def executeCounted {C : ℕ} (p : Program C) :
    ℕ→CachedReferenceExecution.FastState C→ℕ→ℕ→Option (BitState C×ℕ×ℕ)
  | 0, _, _, _ => none
  | fuel+1, s, steps, paid =>
    match CachedReferenceExecution.attempt p s with
    | .stopped final cost => some (final.freeze,steps,paid+cost)
    | .completed next => executeCounted p fuel next.state (steps+1) (paid+next.cost)

private def checkGate (c o R M : Bits) (expected : Bool×Bool) : IO Unit := do
  let current := word c PackedWordPairTable.seed
  let optimal := word o current
  let ratio := word R optimal
  let threshold := word M ratio
  let cfg := allocate (.pair ratio.root threshold.root) threshold
  let tape := [false,true]
  let input : BitState 237 := ⟨cfg.heap,cfg.next,⟨current.root,optimal.root,cfg.root,[]⟩,[],0,tape⟩
  let limit := AdaptiveGatesProgram.instructionBound c.length o.length R.length M.length
  let some (out,k,paid) := executeCounted AdaptiveGatesProgram.program (limit+1)
      (CachedReferenceExecution.FastState.ofReference input) 0 0
    | throw (IO.userError "adaptive gate missed its charged halt")
  let final := eraseState out
  let some (ready,active) := pair final.heap final.registers.d | throw (IO.userError "missing adaptive flags")
  unless final.heap[ready]? == some (.flag expected.1) && final.heap[active]? == some (.flag expected.2) &&
    out.pc == 7 && out.stack.isEmpty && out.source == tape && out.heap.take input.heap.length == input.heap && 0 < paid do
    throw (IO.userError "adaptive gate returned a different result")
  IO.println s!"PASS physical adaptive gates current {value c}, optimum {value o}, ratio {value R}, threshold {value M}, flags {expected}, {k} instructions, paid {paid}"

private def checkRound : IO Unit := do
  let adjacency : PairFlags 2 := #v[#v[false,false],#v[false,false]]
  let active : PairFlags 2 := #v[#v[false,true],#v[false,false]]
  let z : Row 2 := #v[0,0]
  let d : Data 2 := ⟨active,#v[false,false],#v[#v[z,z],#v[z,z]],0,0⟩
  let original := RetainedMassTableProgram.pairOrder 2
  let seed := PackedWordPairTable.seed
  let labels := storeList word [[],[true]] seed
  let matrix := storeList word (GraphRelaxationRefinement.matrix adjacency) labels
  let graph := allocate (.pair labels.root matrix.root) matrix
  let n := word (2 : ℕ).bits graph
  let one := word [true] n
  let roundCfg := allocate (.pair n.root one.root) one
  let roundCtx := allocate (.pair graph.root roundCfg.root) roundCfg
  let before := allocate (.pair matrix.root n.root) roundCtx
  let grid := word [true] before
  let labelsGrid := allocate (.pair labels.root grid.root) grid
  let shared := allocate (.pair before.root labelsGrid.root) labelsGrid
  let pairs := storeList labelPair original shared
  let refreshCtx := allocate (.pair pairs.root shared.root) pairs
  let static := allocate (.pair roundCtx.root refreshCtx.root) refreshCtx
  let R := word (2 : ℕ).bits static
  let M := word [] R
  let gates := allocate (.pair R.root M.root) M
  let params := allocate (.pair static.root gates.root) gates
  let demands := storeList word (active.toList.map Vector.toList) params
  let cut := word d.cut.toList demands
  let masks := allocate (.pair demands.root cut.root) cut
  let packed := allocate (.pair masks.root seed.root) masks
  let weights := storeList (storeList word) (List.replicate 4 (List.replicate 2 [])) packed
  let free := allocate (.flag false) weights
  let weightsFree := allocate (.pair weights.root free.root) free
  let runtime := allocate (.pair weightsFree.root seed.root) weightsFree
  let live := allocate (.pair packed.root runtime.root) runtime
  let candidate := allocate (.pair weights.root seed.root) live
  let cache := allocate (.pair live.root candidate.root) candidate
  let trials := allocate (.pair seed.root seed.root) cache
  let literal := [false,false,true,false]
  let initial : BitState 401 := ⟨trials.heap,trials.next,⟨demands.root,grid.root,trials.root,pairs.root⟩,[],0,literal⟩
  let eCap := PhysicalEpochInputProgram.instructionBound 2 1 1
  let some (epoch,_) := GuardedReferenceExecution.execute PhysicalEpochInputProgram.program (eCap+1) initial 0
    | throw (IO.userError "fair epoch did not provide the selected demand")
  let e := eraseState epoch
  let some (order,cells) := pair e.heap e.registers.d | throw (IO.userError "missing epoch order and cells")
  let some (selected,_) := pair e.heap order | throw (IO.userError "missing selected demand")
  let some (left,right) := pair e.heap selected | throw (IO.userError "missing selected demand labels")
  unless PhysicalCoverReader.readWord e.heap left == some [] && PhysicalCoverReader.readWord e.heap right == some [true] &&
    epoch.source == [true,false] && epoch.pc == 3 do throw (IO.userError "fair epoch returned a different demand or suffix")
  let round : BitState 6878 := ⟨epoch.heap,epoch.next,⟨selected.bits,cells.bits,params.root,cache.root⟩,[],0,epoch.source⟩
  let some (out,k,paid) := executeCounted AdaptiveRoundRefreshProgram.program 50000
      (CachedReferenceExecution.FastState.ofReference round) 0 0
    | throw (IO.userError "round followed by refresh failed to halt")
  let final := eraseState out
  let some (live,best) := pair final.heap final.registers.d | throw (IO.userError "missing updated cache fields")
  let some (current,newRuntime) := pair final.heap live | throw (IO.userError "missing updated live state")
  let some (newMasks,newMass) := pair final.heap current | throw (IO.userError "missing updated masks and mass")
  let some (remaining,newCut) := pair final.heap newMasks | throw (IO.userError "missing updated flags")
  let some (newWeights,newOptimal) := pair final.heap best | throw (IO.userError "missing refreshed weights and optimum")
  let read := PhysicalCoverReader.readWord final.heap
  let some refs := PhysicalCoverReader.readList final.heap some final.heap.length newWeights
    | throw (IO.userError "missing refreshed row pointers")
  let some values := refs.mapM (PhysicalCoverReader.readList final.heap read final.heap.length)
    | throw (IO.userError "missing refreshed table")
  let expected := (EncodedRoundingState.roundData d (0,1)
    (PhysicalSampledRoundProgram.cut (EpochSelectedRoundProgram.enumeration 2) adjacency d (0,1) [false])).1
  unless PhysicalCoverReader.readList final.heap read final.heap.length remaining == some [[false,false],[false,false]] &&
      read newCut == some expected.cut.toList && read newMass == some [] && read newOptimal == some [] &&
      values == List.replicate 4 (List.replicate 2 []) && refs == List.replicate 4 (refs[0]?.getD 0) &&
      newRuntime == value runtime.root &&
      out.pc == 4 && out.stack.isEmpty && out.source == epoch.source && out.heap.take round.heap.length == round.heap && 0 < paid do
    throw (IO.userError "round and refresh did not use the updated remaining demands")
  IO.println s!"PASS fair epoch to round and candidate refresh, remaining empty, cut {expected.cut.toList}, current 0, optimum 0, {k} instructions, paid {paid}"

def main : IO Unit := do
  checkGate [true,true] [false,false] [false,true] [] (true,false)
  checkGate (5 : ℕ).bits (2 : ℕ).bits (2 : ℕ).bits [true] (false,false)
  checkGate (4 : ℕ).bits (2 : ℕ).bits (2 : ℕ).bits (9 : ℕ).bits (true,false)
  checkGate (4 : ℕ).bits (2 : ℕ).bits (2 : ℕ).bits (8 : ℕ).bits (true,true)
  checkRound
