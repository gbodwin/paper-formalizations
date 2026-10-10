import DirectedFlowCutGap.ImmutableReferenceTerminal
open DirectedFlowCutGap
open ImmutableReferenceSimulation ImmutableReferenceTerminal BinaryArithmetic EncodedSequenceAccess

private def initial : BitState 1 :=
  ⟨[.nil],[true,false],⟨[false,false],[false,false],[false,false],[false,false]⟩,
    [],0,[true,false]⟩
private def fixed (i : Instruction 1) : Program 1 := fun _ => i
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def checkStopped (i : Instruction 1) (s : BitState 1) (q : Nat) : IO Unit := do
  let r := attempt (fixed i) s
  check (r.result == none && r.operations == q) "terminal result and retained operation charge"
  check (tick (fixed i) s == none && tickNatural (fixed i) (eraseState s) == none)
    "terminal high/low observation"

def main : IO Unit := do
  checkStopped .halt initial 17
  checkStopped (.ret .r0) initial 17
  let baseRead := (copyBits initial.registers.a).2 + (lookup initial.registers.a initial.heap).2 + 17
  checkStopped (.field .r1 .r0 false 0) initial baseRead
  checkStopped (.emit .r0 0) initial baseRead
  let bad := {initial with registers := {initial.registers with a := [true,false,false]}}
  let badRead := (copyBits bad.registers.a).2 + (lookup bad.registers.a bad.heap).2 + 17
  checkStopped (.branch .r0 0 0 0 0) bad badRead
  check (decide (17 < baseRead ∧ 17 < badRead)) "failed read work is not discarded"
  IO.println s!"PASS terminal halt, return and failed reads; operations=17,{baseRead},{badRead}"
  let move := attempt (fixed (.move .r1 .r0 0)) initial
  check (move.result == tick (fixed (.move .r1 .r0 0)) initial && move.operations == 26)
    "successful move and padded copy charge unchanged"
  let request := attempt (fixed (.request .r0 0)) initial
  match request.result with
  | none => throw (IO.userError "request unexpectedly stopped")
  | some r =>
      check (r.events == [.request true] && r.state.source == [false] && request.operations == r.cost)
        "successful request preserves events, source suffix and charge"
  IO.println s!"PASS terminal extension preserves successful bodies; operations={move.operations},{request.operations}"
  IO.println "PASS all terminal-attempt execution groups"
