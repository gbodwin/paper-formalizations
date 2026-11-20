import DirectedFlowCutGap.CachedHeapBuild

open DirectedFlowCutGap
open BinaryArithmetic ImmutableReferenceSimulation

private def isPair : Option (Cell Bits) → Bool
  | some (.pair [true] []) => true
  | _ => false

def main : IO Unit := do
  let input : Heap := [.nil,.flag true]
  let initial := CachedReferenceHeap.ofList input
  let cell : Cell Bits := .pair [true] []
  let (extended, work) := CachedReferenceHeap.append initial cell
  let initialBlocks := CachedHeapBuild.placements CachedReferenceHeap.empty input 20
  let appendBlocks := CachedHeapCopies.appendBlocks initial cell initialBlocks.1
  unless initial.cells.size == 2 && extended.cells.size == 3 && work > 0 &&
      extended.cellPrefix[3]?.getD 0 == CachedHeapCopies.payloadAfter initial cell &&
      extended.countPrefix[3]?.getD 0 == CachedHeapCopies.addressAfter initial &&
      isPair (CachedReferenceHeap.read extended [false,true]).1 &&
      (CachedReferenceHeap.read extended [true,true]).1.isNone &&
      initialBlocks.1 == 45 && initialBlocks.2 == [(20,3),(23,4),(27,4),(31,4),(35,5),(40,5)] &&
      appendBlocks.1 == 62 && appendBlocks.2 == [(45,5),(50,6),(56,6)] do
    throw (IO.userError "cached storage or its modeled allocation disagrees")
  IO.println s!"PASS initial cache reached {initialBlocks.1}, appended blocks {appendBlocks.2}, final extent {appendBlocks.1}, exact counters and indexed lookup"
