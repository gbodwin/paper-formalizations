import DirectedFlowCutGap.BinaryWeightedSampling
import DirectedFlowCutGap.BinaryRetainedTape

/-! Actual binary weighted construction, selection, and retained-tape effects.
These finite fixtures do not establish a fair-source distribution or the full
adaptive packing/runtime composition. -/
open DirectedFlowCutGap
open BinaryArithmetic
set_option synthInstance.maxSize 10000

private structure Source where
  bits : Bits
  calls : Nat
private def sourceBit : StateM Source Bool := do
  let s ← get
  set (⟨s.bits.tail,s.calls+1⟩ : Source)
  pure (s.bits.headD false)
private def labelA : Bits := [false,true,false,false]
private def labelB : Bits := [true,false]
private def half : BinaryRational.Fraction := ⟨[true,false],[false,true,false],by decide⟩
private def twoThirds : BinaryRational.Fraction := ⟨[false,true,false],[true,true,false],by decide⟩
private def input : BinaryWeightedMasses.Input := [(labelA,half),(labelB,twoThirds)]
private def fuel : Bits := [false,true,false]
private def ticketBits (i : Nat) : Bits := (List.range 3).map fun j => decide ((i / 2^j) % 2 = 1)
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def constructionCases : IO Unit := do
  let encoded := BinaryWeightedMasses.encode input
  check (value encoded.denominator == 6) "common denominator"
  check (BinaryWeightedMasses.data encoded.masses == [(labelA,3),(labelB,4)]) "exact normalized integer masses and stored labels"
  let prepared := BinaryWeightedSampling.prepare input
  check (value prepared.total == 7 && value prepared.denominator == 6) "prepared total and denominator"
  check (decide (0 < prepared.operations ∧ prepared.operations ≤ BinaryWeightedSampling.preparationBound 2 3 4)) "preparation charge"
  let empty := BinaryWeightedSampling.prepare []
  check (value empty.total == 0 && value empty.denominator == 1 && empty.masses == []) "empty preparation"
  IO.println s!"PASS weighted binary preparation; operations={prepared.operations}"

private def ticketCases : IO Unit := do
  let mut first : Nat := 0
  let mut second : Nat := 0
  for i in List.range 7 do
    let (out,source) := (BinaryWeightedSampling.sample sourceBit input fuel).run ⟨ticketBits i,0⟩
    check (!out.zeroTotal && !out.failed && value out.trials == 1 && value out.consumed == 3 && source.calls == 3 && source.bits == []) "accepted ticket metadata/source effects"
    let expected := if i < 3 then labelA else labelB
    check (out.label == (some expected : Option Bits)) "exact binary ticket interval selection"
    if out.label == (some labelA : Option Bits) then first := first+1 else second := second+1
  check (first == 3 && second == 4) "finite ticket counts"
  IO.println "PASS weighted all seven tickets; counts=3,4"

private def rejectionCases : IO Unit := do
  let (retried,afterRetry) := (BinaryWeightedSampling.sample sourceBit input fuel).run ⟨[true,true,true,false,false,false],0⟩
  check (!retried.failed && !retried.zeroTotal && retried.label == (some labelA : Option Bits)) "rejection then accepted ticket"
  check (value retried.trials == 2 && value retried.consumed == 6 && afterRetry.calls == 6) "rejection source effects"
  let (exhausted,afterExhaustion) := (BinaryWeightedSampling.sample sourceBit input fuel).run ⟨[true,true,true,true,true,true],0⟩
  check (exhausted.failed && !exhausted.zeroTotal && exhausted.label == (some labelA : Option Bits)) "legal exhaustion default"
  check (value exhausted.trials == 2 && value exhausted.consumed == 6 && afterExhaustion.calls == 6) "exhaustion source effects"
  let zeros : BinaryWeightedMasses.Input := [(labelA,BinaryRational.zero),(labelB,BinaryRational.zero)]
  let (zero,afterZero) := (BinaryWeightedSampling.sample sourceBit zeros fuel).run ⟨[true],0⟩
  check (zero.zeroTotal && zero.failed && zero.label == none && value zero.trials == 0 && value zero.consumed == 0) "zero total result"
  check (afterZero.calls == 0 && afterZero.bits == [true]) "zero total consumes no bits"
  let (noFuel,afterNoFuel) := (BinaryWeightedSampling.sample sourceBit input []).run ⟨[true],0⟩
  check (noFuel.failed && noFuel.label == (some labelA : Option Bits) && afterNoFuel.calls == 0) "zero fuel consumes no bits"
  IO.println s!"PASS weighted rejection and exhaustion; operations={retried.operations},{exhausted.operations},{zero.operations}"

private def tapeCases : IO Unit := do
  let (counted,q) := BinaryRetainedTape.count ([5,9] : List Nat)
  check (value counted == 2 && q == 27) "literal retained-element count"
  check (BinaryRetainedTape.decodeIndex [false,true,false] == (2,25)) "paid padded-index decoding"
  let (sampled,source) := (BinaryRetainedTape.tape sourceBit fuel [true,true] (L := 3) (by decide) (by decide)
      ([5,9] : List Nat) [false,true] (by decide) BinarySamplerMetadata.empty).run ⟨[],0⟩
  let tape := sampled.1
  let ledger := sampled.2
  check (tape.1.1.val == 0 && tape.1.2.1.val == 0 && tape.2.1.val == 0 && tape.2.2.1.val == 0) "actual permutation/cell tape values"
  check (!ledger.failed && value ledger.draws == 4 && value ledger.trials == 4 && value ledger.consumed == 7 && source.calls == 7) "retained tape physical counters"
  let initial : BinarySamplerMetadata.Ledger := ⟨true,[true],[true,false],[true],10⟩
  let (continued,continuedSource) := (BinaryRetainedTape.tape sourceBit fuel [true,true] (L := 3) (by decide) (by decide)
      ([5,9] : List Nat) [false,true] (by decide) initial).run ⟨[],0⟩
  check (continued.2.failed && value continued.2.draws == 5 && value continued.2.trials == 5 && value continued.2.consumed == 8 && continuedSource.calls == 7) "entering ledger retained exactly once"
  check (decide (0 < ledger.operations ∧ 10 ≤ continued.2.operations)) "ledger operation accumulation"
  let (empty,emptySource) := (BinaryRetainedTape.tape sourceBit fuel [true,true] (L := 3) (by decide) (by decide)
      ([] : List Nat) [] (by decide) BinarySamplerMetadata.empty).run ⟨[true],0⟩
  check (emptySource.calls == 0 && emptySource.bits == [true] && empty.2.operations == 16 && value empty.2.draws == 0) "empty retained tape charges and no draws"
  IO.println s!"PASS retained tape effects and entering ledger; operations={ledger.operations},{continued.2.operations},{empty.2.operations}"

def main : IO Unit := do
  constructionCases
  ticketCases
  rejectionCases
  tapeCases
  IO.println "PASS all four weighted and tape execution groups"
