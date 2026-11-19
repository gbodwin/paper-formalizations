import DirectedFlowCutGap.AdaptiveControllerExecution
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

private def storeKey (p : Pair 3) (s : Store) : Store :=
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

private def reachRestart (target : Fin 7320) :
    ℕ → CachedReferenceExecution.FastState 7320 → ℕ → ℕ →
      Option (BitState 7320×ℕ×ℕ)
  | 0, _, _, _ => none
  | fuel+1, s, steps, paid =>
    if s.pc == target then some (s.freeze,steps,paid)
    else
      match CachedReferenceExecution.attempt CacheStabilizeProgram.program s with
      | .stopped _ _ => none
      | .completed next => reachRestart target fuel next.state (steps+1) (paid+next.cost)

private inductive Case
  | selected | noPairs | staleHead | unready
deriving BEq, Repr

private def caseLabel : Case → String
  | .selected => "selected demand"
  | .noPairs => "empty order"
  | .staleHead => "stale demand"
  | .unready => "unready cache"

private def check (mode : Case) (restartOnly : Bool := false) : IO Unit := do
  let adjacency : PairFlags 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let active : PairFlags 3 := #v[#v[false,false,true],#v[false,false,false],#v[false,false,false]]
  let z : Row 3 := #v[0,0,0]
  let weights : Family 3 := #v[#v[z,z,#v[0,3,0]],#v[z,z,z],#v[z,z,z]]
  let candidate : Family 3 := #v[#v[z,z,#v[0,1,0]],#v[z,z,z],#v[z,z,z]]
  let original := RetainedMassTableProgram.pairOrder 3
  let seed := PackedWordPairTable.seed
  let labels := storeList word ((List.finRange 3).map fun i => i.val.bits) seed
  let matrix := storeList word (GraphRelaxationRefinement.matrix adjacency) labels
  let graph := allocate (.pair labels.root matrix.root) matrix
  let n := word (3 : ℕ).bits graph
  let one := word [true] n
  let roundCfg := allocate (.pair n.root one.root) one
  let roundCtx := allocate (.pair graph.root roundCfg.root) roundCfg
  let originalGraph := allocate (.pair matrix.root n.root) roundCtx
  let grid := word [true] originalGraph
  let labelsGrid := allocate (.pair labels.root grid.root) grid
  let shared := allocate (.pair originalGraph.root labelsGrid.root) labelsGrid
  let pairs := storeList storeKey original shared
  let refreshCtx := allocate (.pair pairs.root shared.root) pairs
  let static := allocate (.pair roundCtx.root refreshCtx.root) refreshCtx
  let ratio : ℕ := if mode==.unready then 2 else 4
  let R := word ratio.bits static
  let M := word [true] R
  let gates := allocate (.pair R.root M.root) M
  let params := allocate (.pair static.root gates.root) gates
  let demands := storeList word (active.toList.map Vector.toList) params
  let cut := word [false,false,false] demands
  let masks := allocate (.pair demands.root cut.root) cut
  let mass := word [true,true,false,false] masks
  let packed := allocate (.pair masks.root mass.root) mass
  let pad := fun i : ℕ => i.bits++[false,false]
  let regime := allocate .nil packed
  let weightsAt := storeList (storeList word) (original.map fun p => (row weights p).toList.map pad) regime
  let free := allocate (.flag false) weightsAt
  let weightsFree := allocate (.pair weightsAt.root free.root) free
  let scale := word [true,true,false] weightsFree
  let runtime := allocate (.pair weightsFree.root scale.root) scale
  let state := allocate (.pair packed.root runtime.root) runtime
  let optTable := storeList (storeList word) (original.map fun p => (row candidate p).toList.map Nat.bits) state
  let optMass := word [true,false,false] optTable
  let best := allocate (.pair optTable.root optMass.root) optMass
  let cache := allocate (.pair state.root best.root) best
  let staleOrder := storeList storeKey [(2,0),(0,2)] cache
  let trials := allocate (.pair seed.root seed.root) staleOrder
  let twice := allocate (.pair seed.root trials.root) trials
  let source := [true,false,true]
  let regs := ⟨twice.root,seed.root,params.root,cache.root⟩
  if restartOnly then
    let initial : BitState 7320 := ⟨twice.heap,twice.next,regs,[],0,source⟩
    let refreshEntry := CacheStabilizeProgram.advanceLabel (CacheAdvanceProgram.refreshLabel 2)
    let solverEntry := CacheStabilizeProgram.advanceLabel
      (CacheAdvanceProgram.refreshLabel (AdaptiveRoundRefreshProgram.refreshLabel 0))
    let some (out,steps,paid) := reachRestart refreshEntry 10000
        (CachedReferenceExecution.FastState.ofReference initial) 0 0
      | throw (IO.userError "unready restart did not enter refresh with the installed state")
    let live := eraseState out
    let some (packed,runtime) := pair live.heap live.registers.b | throw (IO.userError "missing installed state")
    let some (retainedMasks,current) := pair live.heap packed | throw (IO.userError "missing installed masks or mass")
    let some (ctx,newScale) := pair live.heap runtime | throw (IO.userError "missing installed scale")
    let some (installed,_) := pair live.heap ctx | throw (IO.userError "missing installed weight pointer")
    unless retainedMasks == value masks.root && current == value optMass.root && installed == value optTable.root &&
        PhysicalCoverReader.readWord live.heap newScale == some [false,false,true,true,false] do
      throw (IO.userError "restart did not install the actual cached records")
    let some (called,total,charge) := reachRestart solverEntry 10000
        (CachedReferenceExecution.FastState.ofReference out) steps paid
      | throw (IO.userError "stabilization did not reach candidate refresh entry")
    let input := eraseState called
    let some (heldCut,heldScale) := pair input.heap input.registers.d
      | throw (IO.userError "missing refresh query cutoff and scale")
    unless called.source == source && called.heap.take initial.heap.length == initial.heap &&
        input.registers.a == value pairs.root && input.registers.b == value demands.root &&
        input.registers.c == value shared.root && heldCut == value cut.root && heldScale == newScale do
      throw (IO.userError "refresh did not pass the actual original labels, live masks, and installed scale")
    IO.println s!"PASS unready restart installed scale 12 and reached candidate refresh entry with the live masks, {total} instructions, paid {charge} before its first instruction"
    return
  if mode==.selected then
    let prepared : BitState 118 := ⟨twice.heap,twice.next,regs,[],0,source⟩
    let some (out,k,paid) := executeCounted ControllerEpochParameters.program 100000
        (CachedReferenceExecution.FastState.ofReference prepared) 0 0
      | throw (IO.userError "epoch parameters did not halt")
    let final := eraseState out
    let some (param,zeroFlag) := pair final.heap final.registers.d | throw (IO.userError "missing refreshed epoch parameters")
    let some (persisted,gates) := pair final.heap param | throw (IO.userError "missing refreshed epoch gate pair")
    let some (ratio,threshold) := pair final.heap gates | throw (IO.userError "missing frozen threshold")
    unless out.pc == 4 && out.source == source && persisted == value static.root && ratio == value R.root &&
        final.heap[zeroFlag]? == some (.flag false) && PhysicalCoverReader.readWord final.heap threshold == some [true,true] do
      throw (IO.userError "did not snapshot the actual current mass and zero optimum flag")
    IO.println s!"PASS froze padded current mass as canonical threshold 3, optimum nonzero, {k} instructions, paid {paid}"
    for (fuel,root) in [(0,seed.root),(2,twice.root)] do
      let initial : BitState 7320 := ⟨twice.heap,twice.next,regs.set .r0 root,[],0,source⟩
      let some (done,k,paid) := executeCounted CacheStabilizeProgram.program 100000
          (CachedReferenceExecution.FastState.ofReference initial) 0 0
        | throw (IO.userError "ready stabilization did not halt")
      unless done.pc == 1 && done.source == source && done.registers.d == cache.root &&
          done.heap.take initial.heap.length == initial.heap do
        throw (IO.userError "ready stabilization changed the cached family or tape")
      IO.println s!"PASS retained cache through {fuel} stored ready steps, {k} instructions, paid {paid}"
  if mode==.unready then
    let initial : BitState 48 := ⟨twice.heap,twice.next,regs,[],0,source⟩
    let some (out,k,paid) := executeCounted CacheInstallProgram.program 100000
        (CachedReferenceExecution.FastState.ofReference initial) 0 0
      | throw (IO.userError "cache installation failed")
    let final := eraseState out
    let some (state,runtime) := pair final.heap final.registers.d | throw (IO.userError "missing installed state")
    let some (retainedMasks,current) := pair final.heap state | throw (IO.userError "missing installed masks or current")
    let some (ctx,newScale) := pair final.heap runtime | throw (IO.userError "missing installed scale")
    let some (installed,_) := pair final.heap ctx | throw (IO.userError "missing installed table")
    unless out.pc == 3 && out.source == source && retainedMasks == value masks.root && current == value optMass.root &&
        installed == value optTable.root && PhysicalCoverReader.readWord final.heap newScale == some [false,false,true,true,false] &&
        out.heap.length == initial.heap.length+6 do
      throw (IO.userError "install did not reuse the actual cache pointers and shift the scale")
    IO.println s!"PASS installed the actual table and mass pointers, scale 12, six appended cells, {k} instructions, paid {paid}"
  let literal := [false,false,true,false]
  let epochInput : BitState 401 := ⟨trials.heap,trials.next,⟨demands.root,grid.root,trials.root,pairs.root⟩,[],0,literal⟩
  let cap := PhysicalEpochInputProgram.instructionBound 3 1 1
  let some (epoch,_) := GuardedReferenceExecution.execute PhysicalEpochInputProgram.program (cap+1) epochInput 0
    | throw (IO.userError "fair epoch fixture did not materialize")
  let ep := eraseState epoch
  let some (order,cells) := pair ep.heap ep.registers.d | throw (IO.userError "missing fair order or cells")
  let order := match mode with
    | .noPairs => regime.root
    | .staleHead => staleOrder.root
    | _ => order.bits
  let initial : BitState 7324 := ⟨epoch.heap,epoch.next,⟨order,cells.bits,params.root,cache.root⟩,[],0,epoch.source⟩
  let some (out,k,paid) := executeCounted EpochScanProgram.program 100000
      (CachedReferenceExecution.FastState.ofReference initial) 0 0
    | throw (IO.userError "fixed epoch scan did not halt")
  let final := eraseState out
  unless out.pc == 1 && out.stack.isEmpty && out.source == [true,false] &&
      out.heap.take initial.heap.length == initial.heap && 0 < paid do
    throw (IO.userError "scan did not preserve the source and heap prefix")
  if mode==.selected then
    let some (live,candidate) := pair final.heap final.registers.d | throw (IO.userError "missing scanned cache")
    let some (massState,keptRuntime) := pair final.heap live | throw (IO.userError "missing scanned state")
    let some (masks,current) := pair final.heap massState | throw (IO.userError "missing scanned mass")
    let some (remaining,cut) := pair final.heap masks | throw (IO.userError "missing scanned masks")
    let some (table,optimum) := pair final.heap candidate | throw (IO.userError "missing refreshed optimum")
    let read := PhysicalCoverReader.readWord final.heap
    let some refs := PhysicalCoverReader.readList final.heap some final.heap.length table
      | throw (IO.userError "missing candidate row pointers")
    let some values := refs.mapM (PhysicalCoverReader.readList final.heap read final.heap.length)
      | throw (IO.userError "missing candidate rows")
    unless PhysicalCoverReader.readList final.heap read final.heap.length remaining == some (List.replicate 3 [false,false,false]) &&
      read cut == some [false,true,false] && read current == some [] && read optimum == some [] &&
      keptRuntime == value runtime.root && refs == List.replicate 9 (refs[0]?.getD 0) &&
      values == List.replicate 9 (List.replicate 3 []) do
      throw (IO.userError "active scan did not cut the interior vertex and refresh the emptied state")
    IO.println s!"PASS epoch scan followed actual fair pair (0, 2), cut [false, true, false], current 0, optimum 0, {k} instructions, paid {paid}"
    let whole : BitState 7789 := ⟨trials.heap,trials.next,⟨trials.root,seed.root,params.root,cache.root⟩,[],0,literal⟩
    let some (done,wholeSteps,wholePaid) := executeCounted PhysicalEpochScanProgram.program 100000
        (CachedReferenceExecution.FastState.ofReference whole) 0 0
      | throw (IO.userError "whole fair epoch did not halt")
    let all := eraseState done
    unless done.pc == 4 && done.stack.isEmpty && done.source == [true,false] &&
      done.heap.take whole.heap.length == whole.heap && 0 < wholePaid do
      throw (IO.userError "whole epoch changed the tape suffix or immutable heap")
    let some (wholeState,wholeCandidate) := pair all.heap all.registers.d
      | throw (IO.userError "missing whole-epoch cache")
    let some (wholeMassState,wholeRuntime) := pair all.heap wholeState
      | throw (IO.userError "missing whole-epoch state")
    let some (wholeMasks,wholeCurrent) := pair all.heap wholeMassState
      | throw (IO.userError "missing whole-epoch mask and current mass")
    let some (wholeRemaining,wholeCut) := pair all.heap wholeMasks
      | throw (IO.userError "missing whole-epoch cut")
    let some (wholeTable,wholeOptimum) := pair all.heap wholeCandidate
      | throw (IO.userError "missing whole-epoch refreshed table")
    let readWhole := PhysicalCoverReader.readWord all.heap
    let some wholeRefs := PhysicalCoverReader.readList all.heap some all.heap.length wholeTable
      | throw (IO.userError "missing whole-epoch row pointers")
    let some wholeRows := wholeRefs.mapM (PhysicalCoverReader.readList all.heap readWhole all.heap.length)
      | throw (IO.userError "missing whole-epoch rows")
    unless PhysicalCoverReader.readList all.heap readWhole all.heap.length wholeRemaining ==
        some (List.replicate 3 [false,false,false]) && readWhole wholeCut == some [false,true,false] &&
        readWhole wholeCurrent == some [] && readWhole wholeOptimum == some [] &&
        wholeRuntime == value runtime.root && wholeRefs == List.replicate 9 (wholeRefs[0]?.getD 0) &&
        wholeRows == List.replicate 9 (List.replicate 3 []) do
      throw (IO.userError "whole epoch did not select the actual pair and refresh the emptied state")
    IO.println s!"PASS fixed program drew and scanned the entire epoch, cut [false, true, false], unread [true, false], {wholeSteps} instructions, paid {wholePaid}"
    let some (guarded,guardedPaid) := GuardedReferenceExecution.execute PhysicalEpochScanProgram.program (wholeSteps+1) whole 0
      | throw (IO.userError "guarded whole epoch did not accept the literal tape")
    unless guarded.pc == done.pc && guarded.source == done.source && guarded.heap == done.heap &&
        guarded.next == done.next && guarded.registers.d == done.registers.d && guarded.stack.isEmpty &&
        guardedPaid == wholePaid+(wholeSteps+1)*GuardedReferenceExecution.guardCost 7789 do
      throw (IO.userError "guarded whole epoch disagreed with the counted execution")
    IO.println s!"PASS guarded whole epoch matched the counted result and paid {guardedPaid} including all guards"
    let short := { whole with source := [false] }
    unless (GuardedReferenceExecution.execute PhysicalEpochScanProgram.program 100000 short 0).isNone do
      throw (IO.userError "whole epoch accepted the one-bit prefix")
    IO.println "PASS whole epoch rejected the one-bit tape"

    let fuel := allocate (.pair trials.root twice.root) twice
    let controllerCfg := allocate (.pair params.root fuel.root) fuel
    let input : BitState 15323 :=
      ⟨controllerCfg.heap,controllerCfg.next,⟨twice.root,seed.root,controllerCfg.root,cache.root⟩,[],0,literal⟩
    let controller := AdaptiveControllerProgram.program
    let some (_,controllerSteps,_) := executeCounted controller 100000
        (CachedReferenceExecution.FastState.ofReference input) 0 0
      | throw (IO.userError "represented controller did not terminate")
    let some (completed,charged) := GuardedReferenceExecution.execute controller (controllerSteps+1) input 0
      | throw (IO.userError "guarded controller did not accept the literal tape")
    let ctrl := eraseState completed
    let some (live,best) := pair ctrl.heap ctrl.registers.d | throw (IO.userError "missing final controller cache")
    let some (packed,keptRuntime) := pair ctrl.heap live | throw (IO.userError "missing final controller state")
    let some (masks,current) := pair ctrl.heap packed | throw (IO.userError "missing final controller current mass")
    let some (remaining,cut) := pair ctrl.heap masks | throw (IO.userError "missing final controller masks")
    let some (table,opt) := pair ctrl.heap best | throw (IO.userError "missing final controller optimum")
    let read := PhysicalCoverReader.readWord ctrl.heap
    let some refs := PhysicalCoverReader.readList ctrl.heap some ctrl.heap.length table
      | throw (IO.userError "missing final controller family")
    unless completed.pc == 1 && completed.stack.isEmpty && completed.source == [true,false] &&
        completed.heap.take input.heap.length == input.heap && keptRuntime == value runtime.root &&
        read cut == some [false,true,false] && read current == some [] && read opt == some [] &&
        refs == List.replicate 9 (refs[0]?.getD 0) &&
        PhysicalCoverReader.readList ctrl.heap read ctrl.heap.length remaining == some (List.replicate 3 [false,false,false]) do
      throw (IO.userError "the controller failed to cut, refresh, then terminate at the zero optimum")
    IO.println s!"PASS guarded controller sampled one live epoch, stopped at zero before the second draw, and kept the suffix, {controllerSteps} instructions, paid {charged}"
    unless (GuardedReferenceExecution.execute controller (controllerSteps+1) { input with source := [false] } 0).isNone do
      throw (IO.userError "guarded controller accepted a one-bit input")
    IO.println "PASS guarded controller rejected insufficient tape before the first scan"
  else
    unless final.registers.d == value cache.root do throw (IO.userError "failed head test changed the cache")
    IO.println s!"PASS epoch scan stopped at {caseLabel mode} and preserved cache, {k} instructions, paid {paid}"

def main (args : List String) : IO Unit := do
  if args == ["restart-prefix"] then
    check .unready true
  else
    check .noPairs
    check .unready
    check .staleHead
    check .selected
