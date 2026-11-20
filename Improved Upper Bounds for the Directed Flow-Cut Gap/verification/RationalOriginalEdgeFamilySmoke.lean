import DirectedFlowCutGap.RationalOriginalEdgeFamily

open DirectedFlowCutGap
open scoped NNRat

private def check (A : BinaryFractionalWalkOracle.Adjacency 2) (w : RationalEdgeThresholds.Weights 2)
    (expectedScale expectedLength : ℕ) : IO Unit := do
  let result := RationalOriginalEdgeFamily.adaptive A w 1
  let scale := RationalOriginalEdgeFamily.chooseScale A w 1
  unless scale == expectedScale && result.cuts.length == expectedLength &&
      result.cuts.all (fun X => decide (X = {(0,1)})) do
    throw (IO.userError "the original-factor family changed its scale or selected a wrong cut")
  IO.println s!"PASS original rational family chose scale {scale}, with {result.cuts.length} valid directed-arc cuts"

def main : IO Unit := do
  let zero := BinaryRational.zero
  let one := BinaryRational.one
  let tenth : BinaryRational.Fraction := ⟨(1 : ℕ).bits,(10 : ℕ).bits,by decide⟩
  check #v[#v[false,true],#v[false,false]] #v[#v[zero,one],#v[zero,zero]] 2 21
  check #v[#v[true,true],#v[true,true]] #v[#v[tenth,one],#v[tenth,tenth]] 4 57
  let path : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let some cut := RationalExactEdgeOracle.selectAvoiding path [(0,2)] {(0,1)} (fun _ => 1) |
    throw (IO.userError "no cut was produced with the first edge excluded")
  unless decide (cut = {(1,2)}) do
    throw (IO.userError "the cut checker removed the excluded arc from the graph")
  IO.println "PASS excluded first arc remained on the original path, forcing the second arc"
  let trivialFamily := RationalOriginalEdgeFamily.adaptive
    (#v[#v[false]] : BinaryFractionalWalkOracle.Adjacency 1) #v[#v[zero]] 0
  unless decide (trivialFamily.cuts = [∅]) do
    throw (IO.userError "the zero-factor family did not return its empty cut")
  IO.println "PASS zero factor returned the one-cut empty family"
  let A : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let w : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
  let suffix := [true,false,true]
  let width := FairBitWords.width 21
  let tape := List.replicate width false ++ suffix
  let some ((some sample,paid),(rest,used)) := RationalOriginalEdgeFamily.draw A w 1 1 tape |
    throw (IO.userError "the first indexed cut was not drawn from the original family")
  unless decide (sample = {(0,1)}) && rest == suffix && used == width && 0 < paid do
    throw (IO.userError "the family draw changed the expected cut, suffix or bit count")
  let some ((none,_),(rejected,read)) := RationalOriginalEdgeFamily.draw A w 1 0 tape |
    throw (IO.userError "the zero-trial draw did not retain rejection")
  unless rejected == tape && read == 0 do
    throw (IO.userError "zero-trial rejection consumed a bit")
  IO.println s!"PASS original-factor indexed draw used {used} bits, kept {rest}, and zero-trial rejection left the tape intact"
