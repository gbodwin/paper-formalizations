import DirectedFlowCutGap.ImmutableReferenceSimulation

/- Prepared executable checks only; not yet run. In particular these exercise
   the actual compiled Lean functions, not a second arithmetic model. -/
open DirectedFlowCutGap.ImmutableReferenceSimulation
open DirectedFlowCutGap.BinaryArithmetic

private def testProgram : Program 10 := fun pc =>
  match pc.val with
  | 0 => .request .r0 ⟨1,by decide⟩
  | 1 => .emit .r0 ⟨2,by decide⟩
  | 2 => .make .r1 (.pair .r0 .r2) ⟨3,by decide⟩
  | 3 => .call ⟨7,by decide⟩ ⟨4,by decide⟩ .r3
  | 4 => .emit .r3 ⟨5,by decide⟩
  | 7 => .field .r3 .r1 false ⟨8,by decide⟩
  | 8 => .move .r2 .r3 ⟨9,by decide⟩
  | 9 => .ret .r2
  | _ => .halt

private def initial (source : Bits) : BitState 10 :=
  ⟨[.nil],[true,false],⟨[false,false],[false,false],[false,false],[false,false]⟩,
    [],⟨0,by decide⟩,source⟩

private def evaluate {C : ℕ} (p : Program C) : ℕ → BitState C → Option (BitState C × List Event × ℕ)
  | 0,s => some (s,[],0)
  | n+1,s => do
      let r ← tick p s
      let (out,events,q) ← evaluate p n r.state
      pure (out,r.events++events,r.cost+q)

private def test (source : Bits) (b : Bool) : Bool :=
  match evaluate testProgram 8 (initial source) with
  | none => false
  | some (out,events,q) =>
      out.heap == [.nil,.flag b,.pair [true,false] [false,false]] &&
      out.next == [true,true] &&
      out.registers == ⟨[true,false],[false,true],[false,false],[true,false]⟩ &&
      out.stack == [] && out.pc.val == 5 && out.source == source.tail &&
      events == [.request b,.emit b,.emit b] && q == 678

#eval do
  unless test [true,false] true do
    throw (IO.userError "Eight-step request/call/emit fixture failed")
  unless test [] false do
    throw (IO.userError "Exhausted sequential-source fixture failed")
  unless (lookup [false,false,false] [.flag true]).1 == some (Cell.flag true : Cell Bits) do
    throw (IO.userError "Padded zero address fixture failed")
  unless (lookup [true,false,false] [.flag true]).1 == none do
    throw (IO.userError "Out-of-range address fixture failed")
  IO.println "Four exact Lean execution fixtures passed."
