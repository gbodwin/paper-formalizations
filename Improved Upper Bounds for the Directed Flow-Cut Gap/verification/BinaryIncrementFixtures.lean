import DirectedFlowCutGap.BinaryIncrementProgram
namespace DirectedFlowCutGap.BinaryIncrementProgram.Fixtures
open ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor BinaryArithmetic

def source : Bits := [true,false,true,false]

def start (word : Bits) : NaturalState 16 :=
  let p := construct word
  state (eraseHeap p.heap) (value p.next) (value p.root) 91 37 12 [] source 15

/-- A bounded fixture runner uses the actual instruction tick, not increment. -/
def runTicks : ℕ → NaturalState 16 → Option (NaturalState 16)
  | 0,s => some s
  | n+1,s => (tickNatural program s).bind fun r => runTicks n r.state

def readWord : ℕ → NaturalHeap → ℕ → Option Bits
  | 0,_,_ => none
  | n+1,heap,root => match heap[root]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readWord n heap tail).map (fun bs => b::bs)
      | _ => none
    | _ => none

def check (word expected : Bits) (ticks allocs : ℕ) : Bool :=
  match runTicks ticks (start word) with
  | none => false
  | some s =>
      decide (readWord 12 s.heap s.registers.d = some expected ∧
        s.heap.take (start word).heap.length = (start word).heap ∧
        s.heap.length = (start word).heap.length + allocs ∧
        s.next = s.heap.length ∧ s.source = source ∧ s.pc = 14 ∧ s.stack = [] ∧
        s.registers.a = (start word).registers.a ∧ s.registers.b = 91 ∧
        s.registers.c = 37 ∧ tickNatural program s = none)

theorem empty_fixture : check [] [true] 6 3 = true := by decide
-- A false low digit terminates immediately and shares the remaining padded tail.
theorem false_head_fixture : check [false,true,false] [true,true,false] 8 2 = true := by decide
-- All digits carry, so the result gains one new high true digit.
theorem full_carry_fixture : check [true,true,true] [false,false,false,true] 30 9 = true := by decide
-- Existing high zero padding is preserved exactly, rather than normalized away.
theorem padded_fixture : check [true,false,false,false] [false,true,false,false] 16 4 = true := by decide

#print axioms empty_fixture
#print axioms false_head_fixture
#print axioms full_carry_fixture
#print axioms padded_fixture
end DirectedFlowCutGap.BinaryIncrementProgram.Fixtures
