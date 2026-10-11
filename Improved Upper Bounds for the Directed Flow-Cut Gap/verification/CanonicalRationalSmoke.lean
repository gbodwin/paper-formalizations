import DirectedFlowCutGap.CanonicalRationalSum
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.CanonicalRationalSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → Trace C
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute p fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none

def readFraction (heap : NaturalHeap) (p : ℕ) : Option (Bits×Bits) := do
  let some (.pair num den) := heap[p]? | none
  return (←readBits heap (heap.length+1) num,←readBits heap (heap.length+1) den)

def checkCommon {C : ℕ} (name : String) (initial : BitState C) (t : Trace C) (steps cells : ℕ) : IO Unit := do
  unless t.halted && t.events.isEmpty && t.state.source==initial.source &&
      t.state.stack.isEmpty && t.state.heap.take initial.heap.length==initial.heap &&
      t.state.heap.length==initial.heap.length+cells &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound C (initial.heap.length+1) (initial.heap.length+1) steps do
    throw (IO.userError ("FAILED canonical machine invariants: "++name))

def checkTrim (name : String) (xs : Bits) : IO Unit := do
  let built := PackedWordPairTable.word xs PackedWordPairTable.seed
  let initial : BitState 13 := ⟨built.heap,built.next,⟨built.root,[],[],[]⟩,[],11,[true,false,true]⟩
  let steps := 1+BinaryTrimProgram.steps xs
  let t := execute BinaryTrimProgram.program (steps+1) initial
  checkCommon name initial t steps (trim xs).1.length
  unless t.state.pc==12 && readBits (eraseState t.state).heap (t.state.heap.length+1)
      (value t.state.registers.d)==some (trim xs).1 do
    throw (IO.userError ("FAILED actual trim result: "++name))
  IO.println ("PASS actual trim "++name)

def checkArithmetic (name : String) (product : Bool) (xs ys : Bits) : IO Unit := do
  let x := PackedWordPairTable.word xs PackedWordPairTable.seed
  let y := PackedWordPairTable.word ys x
  let initial : BitState 116 := ⟨y.heap,y.next,⟨x.root,y.root,[],[]⟩,[],CanonicalArithmeticProgram.top product,[false,true,false]⟩
  let steps := CanonicalArithmeticProgram.instructions product xs ys
  let t := execute CanonicalArithmeticProgram.program (steps+1) initial
  let expected := CanonicalArithmeticProgram.result product xs ys
  checkCommon name initial t steps (CanonicalArithmeticProgram.rawCells product xs ys+expected.length)
  unless t.state.pc==115 && readBits (eraseState t.state).heap (t.state.heap.length+1)
      (value t.state.registers.d)==some expected do
    throw (IO.userError ("FAILED actual canonical arithmetic: "++name))
  IO.println ("PASS actual canonical arithmetic "++name)

def wordFraction (x : BinaryRational.Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let n := PackedWordPairTable.word x.num s
  let d := PackedWordPairTable.word x.den n
  PackedWordPairTable.allocate (.pair n.root d.root) d

def checkAddition (name : String) (x y : BinaryRational.Fraction) : IO Unit := do
  let a := wordFraction x PackedWordPairTable.seed
  let b := wordFraction y a
  let initial : BitState 142 := ⟨b.heap,b.next,⟨a.root,b.root,[],[]⟩,[],140,[true,true,false]⟩
  let steps := 1+CanonicalRationalAddition.instructions x y
  let t := execute CanonicalRationalAddition.program (steps+1) initial
  let expected := (BinaryRational.add x y).1
  checkCommon name initial t steps (CanonicalRationalAddition.cells x y)
  unless t.state.pc==141 && readFraction (eraseState t.state).heap (value t.state.registers.d)==
      some (expected.num,expected.den) do
    throw (IO.userError ("FAILED actual rational addition: "++name))
  IO.println ("PASS actual rational addition "++name)

def checkSum (name : String) (xs : List BinaryRational.Fraction) : IO Unit := do
  let built := PackedWordPairTable.construct (xs.map fun x => (x.num,x.den))
  let initial : BitState 158 := ⟨built.heap,built.next,⟨built.root,[],[],[]⟩,[],156,[true,false,false,true]⟩
  let steps := 1+CanonicalRationalSum.steps xs
  let t := execute CanonicalRationalSum.program (steps+1) initial
  let expected := (BinaryFractionalRows.sum xs).1
  checkCommon name initial t steps (CanonicalRationalSum.cells xs)
  unless t.state.pc==157 && readFraction (eraseState t.state).heap (value t.state.registers.d)==
      some (expected.num,expected.den) do
    throw (IO.userError ("FAILED actual canonical rational sum: "++name))
  IO.println ("PASS actual canonical rational sum "++name)

def frac (n d : ℕ) : BinaryRational.Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def padded : BinaryRational.Fraction := ⟨[true,false,false],[false,true,false],by decide⟩
def main : IO Unit := do
  checkTrim "empty" []
  checkTrim "all padding" [false,false,false,false]
  checkTrim "one padded" [true,false,false]
  checkTrim "internal zeros" [false,true,false,true,false,false]
  checkTrim "already canonical" [true,false,true]
  checkArithmetic "empty sum" false [] []
  checkArithmetic "padded carry" false [true,true,false] [true,false,false]
  checkArithmetic "padded zero sum" false [false,false] [false,false,false]
  checkArithmetic "zero product" true [false,false,false] [true,true]
  checkArithmetic "padded product" true [true,true,false] [false,true,false]
  checkArithmetic "empty product" true [true,true] []
  checkAddition "different denominators" (frac 1 1) (frac 1 2)
  checkAddition "both padded" padded padded
  checkAddition "zero left" (frac 0 3) (frac 2 2)
  checkSum "empty list" []
  checkSum "single padded" [padded]
  checkSum "retained pair" [frac 1 1,frac 1 2]
  checkSum "three including zero" [frac 0 2,padded,frac 1 1]
  IO.println "CANONICAL_RATIONAL_ACTUAL_FIXTURES passed: 18 cases"
end DirectedFlowCutGap.CanonicalRationalSmoke

def main : IO Unit := DirectedFlowCutGap.CanonicalRationalSmoke.main
