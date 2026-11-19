import DirectedFlowCutGap.PhysicalIntegerRounding

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState
open CachedReferenceExecution (FastState)
open TotalGuardedPackedExecution (Ready Next)

private def requestLoop : Program 1 := fun _ => .request .r0 0

private theorem request_ready (s : FastState 1) : Acc (Next requestLoop) s := by
  have step {a b : FastState 1} (h : Next requestLoop a b) : a.source.length < b.source.length := by
    obtain ⟨guard,r,reached,rfl⟩ := h
    have comparison := CachedReferenceExecution.attempt_eq requestLoop b
    rw [reached] at comparison
    have same : tick requestLoop b.freeze=some r.freeze := by
      rw [← ImmutableReferenceTerminal.attempt_result,← comparison]
      rfl
    have request : GuardedReferenceExecution.requestCount r.events=1 :=
      (GuardedReferenceExecution.tick_requests same).1
    have consumed := (GuardedReferenceExecution.tick_requests same).2
    change r.state.source=b.source.drop (GuardedReferenceExecution.requestCount r.events) at consumed
    rw [request] at consumed
    have nonempty : b.source ≠ [] := fun empty => guard ⟨rfl,empty⟩
    have positive := List.length_pos_iff.mpr nonempty
    rw [consumed,List.length_drop]
    omega
  exact (Subrelation.wf (fun {_ _} h => step h) (measure (fun u : FastState 1 => u.source.length)).wf).apply s

def main : IO Unit := do
  let tape : Bits := [true,false,true,true,false]
  let plain : BitState 1 := ⟨[],[],⟨[],[],[],[]⟩,[],0,tape⟩
  let state := FastState.ofReference plain
  let result := TotalGuardedPackedExecution.execute requestLoop ⟨state,request_ready state⟩ 0
  unless result.isNone do
    throw (IO.userError "the accessible guarded loop failed to report tape exhaustion")
  IO.println "PASS the total guarded loop rejects after its last available tape bit"
  let adj : PairFlags 0 := #v[]
  let some cut := PhysicalIntegerRounding.hardRun 0 adj 1 tape |
    throw (IO.userError "the total original controller did not halt")
  unless cut.mask.toList == [] && cut.suffix == tape && cut.paid == 36504075 do
    throw (IO.userError "the total original controller changed the result or its guarded charge")
  IO.println s!"PASS the packed original controller halts with identical word and unread tape, paid {cut.paid}"
