import GreedyShortcuts.RawExecutableShortcuts

/-! Actual evaluation of the raw-input construction, including the important
case where already used vertices lie between unused chain vertices. -/
open GreedyShortcuts GreedyShortcuts.DirectedPaths GreedyShortcuts.CanonicalSegments
open SimpleGraph
open LinearDistancePreservers.ConsistentTiebreaking

private def pathEdge {n : ℕ} (u v : Fin n) : Bool := decide (u.val+1=v.val)

private theorem path_monotone {n : ℕ} {s t : Fin n} (p : DWalk s t)
    (hp : Allowed (fun u v => pathEdge u v=true) p) : s.val≤t.val := by
  induction p with
  | nil => exact le_rfl
  | @cons s u t h p ih =>
    have hh := (allowed_cons _ h p).mp hp
    have ht := ih hh.2
    have he : s.val+1=u.val := by simpa [pathEdge] using hh.1
    omega

private theorem pathAcyclic (n : ℕ) : Acyclic (fun u v : Fin n => pathEdge u v=true) := by
  apply (acyclic_iff_reachable_antisymm _).mpr
  intro s t hst hts
  obtain ⟨p,hp⟩ := hst
  obtain ⟨q,hq⟩ := hts
  exact Fin.ext (Nat.le_antisymm (path_monotone p hp) (path_monotone q hq))

#guard FiniteLongestPathDP.maximum (@pathEdge 0) (fun _ => true) = []
#guard FiniteLongestPathDP.maximum (@pathEdge 1) (fun _ => true) = [0]
#guard ComputedChainSearch.find (@pathEdge 5) (fun v => decide (v.val%2=0)) 3 = some [0,2,4]
#guard ComputedChainSearch.find (@pathEdge 5) (fun v => decide (v.val%2=0)) 4 = none
#guard (ComputedChainPacking.pack (@pathEdge 5) 2 5 Finset.univ).1 = [[0,1],[2,3]]
#guard (ComputedChainPacking.pack (@pathEdge 5) 2 5 Finset.univ).2 = {4}
#guard (ComputedChainPacking.pack (@pathEdge 3) 4 3 Finset.univ).1 = []
#guard PathFour.computedHeight 0 = 0
#guard PathFour.computedHeight 2 = 0
#guard PathFour.computedHeight 3 = 1
#guard PathFour.computedHeight 16 = 2
#guard PathFour.computedHeight 17 = 3

/-- info: true -/
#guard_msgs in
#eval RawExecutableShortcuts.output (@pathEdge 0) (pathAcyclic 0) 1 2 == ∅
/-- info: true -/
#guard_msgs in
#eval RawExecutableShortcuts.output (@pathEdge 1) (pathAcyclic 1) 1 2 == ∅
/-- info: true -/
#guard_msgs in
#eval RawExecutableShortcuts.output (@pathEdge 3) (pathAcyclic 3) 1 2 == {(0,2)}
/-- info: true -/
#guard_msgs in
#eval RawExecutableShortcuts.output (@pathEdge 2) (pathAcyclic 2) 2 2 == {(0,1)}
/-- info: true -/
#guard_msgs in
#eval ChainExecutableObjective.stopped (RawExecutableShortcuts.data (@pathEdge 2) (pathAcyclic 2) 2)
    pathEdge 2 (ChainExecutableGreedy.output (RawExecutableShortcuts.data pathEdge (pathAcyclic 2) 2) pathEdge 2)
