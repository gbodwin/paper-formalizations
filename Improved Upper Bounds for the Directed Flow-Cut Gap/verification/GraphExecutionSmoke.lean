import DirectedFlowCutGap.EncodedShortcutMatrixBridge
import DirectedFlowCutGap.BinaryPortMaterialization
import DirectedFlowCutGap.EncodedSurvivorRestriction

/-! New graph-body execution checks. These inspect actual returned stored values
and charges, including padding, malformed reached data, and short-circuit cases.
They do not certify a physical allocator or the whole weighted algorithm. -/
open DirectedFlowCutGap
open BinaryArithmetic EncodedSequenceAccess
set_option synthInstance.maxSize 10000

private def z : Bits := [false,false]
private def o : Bits := [true,false]
private def t : Bits := [false,true,false]
private def vertices : List Bits := [z,o,t]
private def flags (bs : List Bool) : Value := sequence (bs.map Value.flag)
private def table (rows : List (List Bool)) : Value := sequence (rows.map flags)
private def pathGraph : Value := table [[false,true,false],[false,false,true],[false,false,false]]
private def removeMiddle : Value := flags [false,true,false]
private def keepAll : Value := flags [false,false,false]
private def expectedShortcut : Value := table [[false,true,true],[false,false,true],[false,false,false]]
private def bad : Value := .word [true]
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def primitiveCases : IO Unit := do
  let padded := EncodedRestrictedTestExec.flagAt o removeMiddle
  check (padded.1 == (some true : Option Bool)) "padded mask lookup"
  check ((EncodedRestrictedTestExec.flagAt [true,true] removeMiddle).1 == none) "out-of-range mask lookup"
  check ((EncodedRestrictedTestExec.flagAt z bad).1 == none) "malformed reached mask"
  check ((EncodedRestrictedTestExec.endpoint z [] bad).1 == (some true : Option Bool)) "numeric endpoint guard"
  check ((EncodedRestrictedTestExec.endpoint o z bad).1 == none) "non-endpoint reads malformed mask"
  check ((EncodedCellAccess.flag z o pathGraph).1 == (some true : Option Bool)) "stored adjacency cell"
  check (decide (0 < padded.2 ∧ padded.2 ≤ 20*(3+1)*(3+1)+12)) "mask lookup charge"
  IO.println "PASS graph primitives and reached-malformed guards"

private def scanCases : IO Unit := do
  let entries := [EncodedSearchScanExec.keyEntry z,EncodedSearchScanExec.keyEntry o]
  let found := EncodedSearchScanExec.scan (.lookup []) entries
  check (match found.1 with | some (some e) => e.label == z | _ => false) "lookup preserves padded stored label"
  check ((EncodedRootVisitExec.foundScan (.lookup t) entries).1 == (some false : Option Bool)) "absent table root"
  let survivors := EncodedSurvivorExec.scan removeMiddle vertices
  check (survivors.1 == (some [z,t] : Option (List Bits))) "survivor mask and literal padding"
  check ((EncodedSurvivorExec.scan bad []).1 == (some [] : Option (List Bits))) "empty survivor scan does not read mask"
  check ((EncodedSurvivorExec.scan bad [z]).1 == none) "nonempty survivor scan reaches malformed mask"
  check (decide (0 < survivors.2 ∧ survivors.2 ≤ 3*EncodedSurvivorExec.stepBound 3 3+1)) "survivor scan charge"
  IO.println s!"PASS graph scans and survivors; operations={survivors.2}"

private def searchCases : IO Unit := do
  let connected := EncodedShortcutExec.shortcut ⟨z,t,pathGraph,removeMiddle⟩ vertices
  let uncontracted := EncodedShortcutExec.shortcut ⟨z,t,pathGraph,keepAll⟩ vertices
  let reverse := EncodedShortcutExec.shortcut ⟨t,z,pathGraph,removeMiddle⟩ vertices
  check (connected.1 == (some true : Option Bool)) "two-edge shortcut through removed middle"
  check (uncontracted.1 == (some false : Option Bool)) "unremoved middle is not an internal shortcut"
  check (reverse.1 == (some false : Option Bool)) "directed reverse path absent"
  check ((EncodedShortcutExec.shortcut ⟨z,[],bad,bad⟩ vertices).1 == (some false : Option Bool)) "numeric diagonal guard precedes malformed graph"
  check ((EncodedShortcutExec.shortcut ⟨z,t,bad,bad⟩ vertices).1 == none) "reached malformed graph fails"
  check (decide (0 < connected.2 ∧ connected.2 ≤ EncodedShortcutExec.shortcutBound 3 3)) "shortcut search charge"
  IO.println s!"PASS graph root search and diagonal guard; operations={connected.2}"

private def matrixCases : IO Unit := do
  let matrix := EncodedShortcutMatrixExec.matrix pathGraph removeMiddle vertices vertices vertices
  check (matrix.1 == (some expectedShortcut : Option Value)) "complete shortcut matrix"
  check ((EncodedShortcutMatrixExec.matrix bad bad [] [] []).1 == (some Value.empty : Option Value)) "empty matrix guard"
  check (decide (0 < matrix.2 ∧ matrix.2 ≤ EncodedShortcutMatrixExec.matrixBound 3 3 3 3)) "shortcut matrix charge"
  let restricted := EncodedSurvivorRestriction.restrict expectedShortcut [z,t]
  check (restricted.ports == [z,t]) "restriction preserves exact labels"
  check (restricted.adjacency == (some (table [[false,true],[false,false]]) : Option Value)) "survivor adjacency restriction"
  check ((EncodedSurvivorRestriction.restrict bad []).adjacency == (some Value.empty : Option Value)) "empty restriction guard"
  IO.println s!"PASS graph matrix and survivor restriction; operations={matrix.2},{restricted.operations}"

private def portCases : IO Unit := do
  let n : Bits := [true,false]
  let core := BinaryPortDecode.decode n z
  let source := BinaryPortDecode.decode n o
  let sink := BinaryPortDecode.decode n t
  check (core.1.kind == BinaryPortDecode.Kind.core && core.1.index == z) "core decode retains padding"
  check (source.1.kind == BinaryPortDecode.Kind.source && value source.1.index == 0) "source port decode"
  check (sink.1.kind == BinaryPortDecode.Kind.sink && value sink.1.index == 0) "sink port decode"
  check ((BinaryPortDecode.adjacent source.1 sink.1 bad).1 == (some true : Option Bool)) "source-to-sink diagonal skips malformed table"
  check ((BinaryPortDecode.removed source.1 bad).1 == (some false : Option Bool)) "terminal removal guard"
  check ((BinaryPortDecode.removed core.1 bad).1 == none) "core removal reads mask"
  let built := BinaryPortMaterialization.build n (table [[false]]) (flags [true])
  check (built.originalCount == n && value built.portCount == 3 && built.vertices.map value == [0,1,2]) "three-port stored dimensions"
  check (built.adjacency == (some (table [[false,false,false],[false,false,true],[false,false,false]]) : Option Value)) "three-port exact adjacency"
  check (built.removed == (some (flags [true,false,false]) : Option Value)) "three-port exact removal mask"
  let empty := BinaryPortMaterialization.build z bad bad
  check (empty.vertices == [] && empty.adjacency == (some Value.empty : Option Value) && empty.removed == (some Value.empty : Option Value)) "zero-port unused malformed inputs"
  check (decide (0 < built.operations ∧ built.operations ≤ BinaryPortMaterialization.buildBound 1 2)) "three-port construction charge"
  IO.println s!"PASS graph port decode and full materialization; operations={built.operations},{empty.operations}"

def main : IO Unit := do
  primitiveCases
  scanCases
  searchCases
  matrixCases
  portCases
  IO.println "PASS all five new graph execution groups"
