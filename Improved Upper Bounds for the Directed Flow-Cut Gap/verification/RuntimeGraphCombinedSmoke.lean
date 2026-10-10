import DirectedFlowCutGap.EncodedLabelEquality
import DirectedFlowCutGap.EncodedSequenceAccess
import DirectedFlowCutGap.EncodedCellAccess
import DirectedFlowCutGap.EncodedReadTabulation
import DirectedFlowCutGap.EncodedTablePreparation
import DirectedFlowCutGap.EncodedFlagUnion
import DirectedFlowCutGap.BinaryFractionalGuesses

namespace RuntimeGraphCombinedSmoke.Runtime

namespace EncodedFixedBodiesSmoke.LabelSmoke
open DirectedFlowCutGap EncodedLabelEquality

private def pad (k : Key) (p : Nat) : Key :=
  match k with
  | .terminal b => .terminal b
  | .core t v b l => .core t (v++List.replicate p false) b
      (l++List.replicate (p+1) false)

private def width : Key → Nat
  | .terminal _ => 0
  | .core _ v _ l => max v.length l.length

#eval do
  let mut checked : Nat := 0
  for n in List.range 4 do
    for L in List.range 3 do
      let labels := (CandidateEnumeration.make n L).network.enumeration.vertices
      for x in labels do
        for y in labels do
          for p in [0,1,4] do
            let a := pad (canonicalEncoding x) p
            let b := pad (canonicalEncoding y) (4-p)
            let r := equal a b
            let B := max (width a) (width b)
            unless r.1 == decide (x=y) && r.2 ≤ 32*(B+1)+12 do
              throw (IO.userError "network equality or padded-width charge mismatch")
            let q := pairEqual (a,b) (b,a)
            unless q.1 == decide ((x,y)=(y,x)) && q.2 ≤ 64*(B+1)+28 do
              throw (IO.userError "pair-key equality or charge mismatch")
            checked := checked+1
  let huge : Key := .core .sink ((2^128+7).bits++[false,false]) true []
  let hugePad : Key := .core .sink (2^128+7).bits true [false,false,false]
  unless (equal huge hugePad).1 &&
      !(equal huge (.core .source (2^128+7).bits true [])).1 &&
      !(equal huge (.core .sink (2^128+7).bits false [])).1 &&
      !(equal huge (.core .sink (2^128+7).bits true [true])).1 do
    throw (IO.userError "wide or constructor/side/level discrimination mismatch")
  IO.println s!"PASS {checked} actual network and pair-key comparisons, all labels for n=0..3 and L=0..2, independent padding, empty/padded zero, constructor/side/level differences, and 129-bit vertex values"
end EncodedFixedBodiesSmoke.LabelSmoke

namespace EncodedFixedBodiesSmoke.SequenceSmoke
open DirectedFlowCutGap EncodedSequenceAccess

private def sample (i : Nat) : Value :=
  if i%3=0 then .flag (i%2==0)
  else if i%3=1 then .word (i.bits++[false,false,false])
  else .pair (.word [true,false]) (.pair (.flag false) .empty)

#eval do
  let mut reads : Nat := 0
  let mut cells : Nat := 0
  for n in List.range 9 do
    let xs := (List.range n).map sample
    let S := (xs.map Value.size).foldl max 0
    let r := collectValues xs
    unless r.1 == xs && r.2 ≤ 8*(S+2)*(n^2+7*n+1) do
      throw (IO.userError "full-copy collect result or charge mismatch")
    for i in List.range (n+4) do
      for padding in [0,1,4] do
        let ib := i.bits++List.replicate padding false
        let q := read ib (sequence xs)
        unless q.1 == xs[i]? && q.2 ≤ 20*(n+1)*(ib.length+1)+4*S do
          throw (IO.userError "binary sequence read or copied-payload charge mismatch")
        reads := reads+1
    let rows := (List.range n).map fun i => (List.range 5).map fun j => sample (i+2*j)
    let table := sequence (rows.map sequence)
    let T := ((rows.flatten).map Value.size).foldl max 0
    for i in List.range (n+2) do
      for j in List.range 7 do
        let ib := i.bits++[false,false]
        let jb := j.bits++[false,false,false]
        let q := read2 ib jb table
        let B := max ib.length jb.length
        unless q.1 == (rows[i]?).bind (fun row => row[j]?) &&
            q.2 ≤ read2Bound n 5 B T do
          throw (IO.userError "two-read row/payload copy or charge mismatch")
        cells := cells+1
  IO.println s!"PASS {reads} actual binary-controlled reads and {cells} two-read cells, missing indices, padded zero, nested payload copies, and all suffix-copy collect charges"
end EncodedFixedBodiesSmoke.SequenceSmoke

namespace EncodedFixedBodiesSmoke.CallbackSmoke
open DirectedFlowCutGap BinaryArithmetic EncodedSequenceAccess

#eval do
  let mut loops : Nat := 0
  for n in List.range 9 do
    let xs := (List.range n).map fun i => Value.word (i.bits++[false,false])
    let S := (xs.map Value.size).foldl max 0
    for k in List.range (n+1) do
      for pad in [0,1,4] do
        let fuel := k.bits++List.replicate pad false
        let extra := [Value.flag true]
        let out := EncodedReadTabulation.loop (sequence xs) fuel extra
        unless out.1 == some (xs.take k++extra) &&
            out.2 ≤ EncodedReadTabulation.loopBound k n fuel.length S do
          throw (IO.userError "binary descending read loop or accumulator mismatch")
        loops := loops+1
    let count := n.bits++[false,false,false]
    let out := EncodedReadTabulation.tabulate (sequence xs) count
    unless out.1 == some xs &&
        out.2 ≤ EncodedReadTabulation.tabulateBound n count.length S do
      throw (IO.userError "fixed read callback tabulation or full-copy bound mismatch")
    unless (EncodedReadTabulation.tabulate (sequence xs) (n+2).bits).1 == none do
      throw (IO.userError "out-of-range tabulation must reject")
  let input : IntegerAdaptiveExecution.Input 3 4 :=
    { order := []
      cells := Vector.ofFn fun i => Vector.ofFn fun j =>
        ⟨(i.val*3+j.val)%4, Nat.mod_lt _ (by decide)⟩ }
  let words := Vector.ofFn fun i : Fin 3 => Vector.ofFn fun j : Fin 3 =>
    (input.cell (i,j)).val.bits++[false,false,false]
  let flags := Vector.ofFn fun i : Fin 3 => Vector.ofFn fun j : Fin 3 => i.val==j.val
  for i in List.finRange 3 do
    for j in List.finRange 3 do
      let ib := i.val.bits++[false,false]
      let jb := j.val.bits++[false]
      let w := EncodedCellAccess.word ib jb (EncodedCellAccess.wordTable words)
      let f := EncodedCellAccess.flag ib jb (EncodedCellAccess.flagTable flags)
      unless w.1 == some words[i.val][j.val] &&
          w.1.map value == some (input.cell (i,j)).val &&
          f.1 == some flags[i.val][j.val] do
        throw (IO.userError "exact retained Input.cell/flag callback mismatch")
  IO.println s!"PASS {loops} binary descending read loops with retained accumulators, valid/invalid fixed callback tabulations, suffix copies and nine padded Input.cell/flag bodies"
end EncodedFixedBodiesSmoke.CallbackSmoke

namespace EncodedSixBodiesSmoke.TablePreparation
open DirectedFlowCutGap BinaryArithmetic EncodedSequenceAccess EncodedTablePreparation

private def payload (i : Nat) : Value :=
  if i%3=0 then .flag (i%2==0)
  else if i%3=1 then .word (i.bits++[false,false,false])
  else .pair (.word ((2^128+i).bits++[false])) (.word [true,false,false])

#eval do
  let mut reads : Nat := 0
  let mut matrices : Nat := 0
  for n in List.range 7 do
    let rows := (List.range n).map fun i => (List.range ((i+1)%6)).map fun j => payload (i+j)
    let S := (rows.flatten.map Value.size).foldl max 0
    let p := prepareRows rows
    unless p.1 == sequence (rows.map sequence) &&
        p.2 ≤ rowsBound n 5 S && p.1.size ≤ n*(5*(S+1)+2)+1 do
      throw (IO.userError "prepared table data, paid copies or represented size mismatch")
    matrices := matrices+1
    for i in List.range (n+2) do
      for j in List.range 7 do
        let ib := i.bits++[false,false]
        let jb := j.bits++[false,false,false]
        let q := prepareAndRead rows ib jb
        unless q.1 == (rows[i]?).bind (fun row => row[j]?) &&
            q.2 ≤ rowsBound n 5 S+read2Bound n 5 (max ib.length jb.length) S+8 do
          throw (IO.userError "paid preparation/read composition mismatch")
        reads := reads+1
  let input : IntegerAdaptiveExecution.Input 3 4 :=
    { order := []
      cells := Vector.ofFn fun i => Vector.ofFn fun j =>
        ⟨(i.val*3+j.val)%4, Nat.mod_lt _ (by decide)⟩ }
  let raw := (List.finRange 3).map fun i => (List.finRange 3).map fun j =>
    Value.word ((input.cell (i,j)).val.bits++[false,false,false])
  let prepared := prepareRows raw
  for i in List.finRange 3 do
    for j in List.finRange 3 do
      let q := EncodedCellAccess.word (i.val.bits++[false]) (j.val.bits++[false,false]) prepared.1
      unless q.1.map value == some (input.cell (i,j)).val do
        throw (IO.userError "retained prepared table changed original Input.cell")
  IO.println s!"PASS {matrices} finite mixed-payload table preparations, {reads} paid read compositions, padded 129-bit rational-shaped payloads, empty/missing rows and nine original Input.cell queries sharing one prepared table"
end EncodedSixBodiesSmoke.TablePreparation

namespace EncodedSixBodiesSmoke.FlagUnion
open DirectedFlowCutGap BinaryArithmetic EncodedSequenceAccess EncodedTablePreparation

private def flags (n mask : Nat) : RetainedGridState.Flags n :=
  Vector.ofFn fun i => (mask / 2^i.val)%2 == 1

#eval do
  let mut cases : Nat := 0
  for n in List.range 6 do
    for a in List.range (2^n) do
      for b in List.range (2^n) do
        let x := flags n a
        let y := flags n b
        let px := prepareRow (x.toList.map Value.flag)
        let py := prepareRow (y.toList.map Value.flag)
        let source := EncodedRoundingState.union x y
        for padding in [0,1,4] do
          let count := n.bits ++ List.replicate padding false
          let q := EncodedFlagUnion.union px.1 py.1 count
          let bound := EncodedFlagUnion.unionBound n count.length
          unless q.1 == some (EncodedFlagUnion.rowValue source.1.toList) &&
              q.2 ≤ bound && q.2 ≤ bound*source.2 &&
              px.2+py.2+q.2 ≤ 2*rowBound n 2+bound do
            throw (IO.userError "retained flag union changed source data or lost preparation/body charges")
          cases := cases+1
  let left := (prepareRow [.flag true,.flag false]).1
  let malformed := (prepareRow [.flag true,.word [false,false]]).1
  unless (EncodedFlagUnion.union left malformed 2.bits).1 == none &&
      (EncodedFlagUnion.union left left 3.bits).1 == none &&
      (EncodedFlagUnion.union .empty .empty [false,false]).1 == some .empty do
    throw (IO.userError "invalid flag/read rejection or padded zero count mismatch")
  let s : RetainedGridState.Data 3 :=
    { remaining := Vector.replicate 3 (Vector.replicate 3 true)
      cut := #v[true,false,false]
      weights := Vector.replicate 3 (Vector.replicate 3 (Vector.replicate 3 1))
      scale := 4
      current := 18 }
  let cut : RetainedGridState.Flags 3 := #v[false,false,true]
  let old := prepareRow (s.cut.toList.map Value.flag)
  let fresh := prepareRow (cut.toList.map Value.flag)
  let q := EncodedFlagUnion.union old.1 fresh.1 (3.bits++[false,false])
  let round := EncodedRoundingState.roundData s (0,1) cut
  unless q.1 == some (EncodedFlagUnion.rowValue round.1.cut.toList) do
    throw (IO.userError "reached roundData cut did not match retained union")
  IO.println s!"PASS {cases} exhaustive retained flag unions through size five with three paddings, paid preparation/body bounds, malformed and missing reads, padded zero, and reached roundData cut"
end EncodedSixBodiesSmoke.FlagUnion

end RuntimeGraphCombinedSmoke.Runtime

namespace RuntimeGraphCombinedSmoke.Graph

/-! Combined execution driver: the three existing smoke bodies are retained
verbatim below, after removing their repeated import lines. This avoids paying
the large project import startup three times. No additional test is inferred. -/

-- Existing driver: BinaryFractionalGraphSmoke
open DirectedFlowCutGap
open BinaryFractionalWalkOracle BinaryFractionalGraphOracle BinaryFractionalRows

def graphSmokeAdj : Adjacency 3 := Vector.ofFn fun u => Vector.ofFn fun v =>
  decide (u.val+1=v.val ∨ (u.val=0 ∧ v.val=0))

def graphSmokeRow : Row 3 := Vector.replicate 3 BinaryRational.one

def rawSignature {n : ℕ} (s : FractionalCoverRawCore.RawState n) :=
  (s.weights.toList.map (fun q : RawNonnegativeRational.Code => (q.num,q.den)),
   s.best.toList.map (fun q : RawNonnegativeRational.Code => (q.num,q.den)),
   (s.bestCost.num,s.bestCost.den), (s.total.num,s.total.den),
   s.loads.toList.map (fun q : RawNonnegativeRational.Code => (q.num,q.den)),
   s.events.map (fun e => (List.ofFn (fun i : Fin n => decide (i ∈ e.choice.column)),e.choice.bottleneck,(e.amount.num,e.amount.den))))

#eval do
  let p := shortest (IntegralNetworkFlow.ResidualSearch.Enumeration.fin 3)
    graphSmokeAdj (outgoing graphSmokeRow 0) 0 2
  match p.1 with
  | none => throw (IO.userError "reachable demand returned none")
  | some q =>
    unless q.edges=[(0,1),(1,2)] do throw (IO.userError "recovered path mismatch")
    unless (BinaryRational.decode q.cost).num=(BinaryRational.decode q.cost).den do
      throw (IO.userError "binary path cost mismatch")
  let unreachable := shortest (IntegralNetworkFlow.ResidualSearch.Enumeration.fin 3)
    graphSmokeAdj (outgoing graphSmokeRow 2) 2 0
  unless unreachable.1.isNone do throw (IO.userError "unreachable demand had a witness")
  let q := oracle graphSmokeAdj [(2,0),(0,2)] graphSmokeRow (by decide) graphSmokeRow
  unless q.1.mask.toList=[false,true,false] ∧ q.1.bottleneck=1 do
    throw (IO.userError "actual column or bottleneck mismatch")
  let r := solveGraph graphSmokeAdj [(0,2)] graphSmokeRow (by decide)
  let expected := FractionalCoverRawGraph.solveGraph (graph graphSmokeAdj) [(0,2)]
    (BinaryFractionalRows.decodeRow graphSmokeRow) (by decide)
  unless rawSignature (BinaryFractionalCore.decodeState r.state)=rawSignature expected do
    throw (IO.userError "full raw state mismatch")
  unless r.stopTests=27 do throw (IO.userError "fixed stopping scans missing")
  IO.println s!"PASS binary graph path/mask/full-state smoke; retained events={r.state.events.length}; stopping scans={r.stopTests}; operations={r.operations}"

-- Existing driver: BinaryFractionalDispatchSmoke
open DirectedFlowCutGap
open BinaryFractionalWalkOracle BinaryFractionalGraphOracle BinaryFractionalRows

#eval do
  let empty : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let e := BinaryFractionalGuesses.solveInput empty
  match e.1 with
  | .zero mask => unless mask.toList=[] do throw (IO.userError "empty mask mismatch")
  | _ => throw (IO.userError "empty input dispatch mismatch")
  let adjacency : Adjacency 3 := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)
  let costs : Row 3 := #v[BinaryRational.one,BinaryRational.zero,BinaryRational.one]
  let free := BinaryFractionalGuesses.solveInput ⟨adjacency,[(0,2)],costs⟩
  match free.1 with
  | .zero mask => unless mask.toList=[false,true,false] do throw (IO.userError "free mask mismatch")
  | _ => throw (IO.userError "free cut dispatch mismatch")
  let diagonal := BinaryFractionalGuesses.solveInput ⟨adjacency,[(1,1)],costs⟩
  match diagonal.1 with
  | .infeasible d => unless d=(1,1) do throw (IO.userError "wrong infeasible pair")
  | _ => throw (IO.userError "diagonal demand was hidden")
  let direct := BinaryFractionalGuesses.solveInput ⟨adjacency,[(0,1)],costs⟩
  match direct.1 with
  | .infeasible d => unless d=(0,1) do throw (IO.userError "wrong adjacent pair")
  | _ => throw (IO.userError "direct demand was hidden")
  let endpointCosts : Row 3 := #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero]
  let retained := BinaryFractionalDispatch.dispatch adjacency [(0,2)] endpointCosts
  match retained.1 with
  | .positive q => unless q.path.edges=[(0,1),(1,2)] do
      throw (IO.userError "retained endpoint path mismatch")
  | _ => throw (IO.userError "zero-cost endpoints were incorrectly deleted")
  IO.println s!"PASS binary empty/free/diagonal/direct/retained-endpoint dispatch smoke; charges={[e.2,free.2,diagonal.2,direct.2,retained.2]}"

-- Existing driver: BinaryFractionalGuessesSmoke
open DirectedFlowCutGap
open BinaryFractionalWalkOracle BinaryFractionalGraphOracle BinaryFractionalRows

private def rawFields {n : ℕ} (s : FractionalCoverRawCore.RawState n) :=
  (s.weights.toList.map (fun q : RawNonnegativeRational.Code => (q.num,q.den)),
   s.best.toList.map (fun q : RawNonnegativeRational.Code => (q.num,q.den)),
   (s.bestCost.num,s.bestCost.den), (s.total.num,s.total.den),
   s.loads.toList.map (fun q : RawNonnegativeRational.Code => (q.num,q.den)),
   s.events.map (fun e => (List.ofFn (fun i : Fin n => decide (i ∈ e.choice.column)),e.choice.bottleneck,(e.amount.num,e.amount.den))))

#eval do
  let padded : BinaryRational.Fraction := ⟨[true,false,false],[true,false],by decide⟩
  let width := BinaryFractionalGuesses.inputWidth (#v[padded] : Row 1)
  unless BinaryArithmetic.value width.1=1 do throw (IO.userError "padded width disagrees with raw input")
  let adjacency : Adjacency 3 := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)
  let costs : Row 3 := #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero]
  let D : BinaryFractionalGuesses.Input 3 := ⟨adjacency,[(0,2)],costs⟩
  let r := BinaryFractionalGuesses.solveInput D
  match r.1 with
  | .covers states =>
    unless states.length=9 do throw (IO.userError "full guess range missing entries")
    unless (states.map BinaryFractionalCore.Result.stopTests).sum=243 do
      throw (IO.userError "fixed stopping scans were skipped")
    let raw := FractionalCoverRawGuesses.solveInput (BinaryFractionalGuesses.decodeInput D)
    match raw with
    | .covers expected =>
      unless states.map (fun s => rawFields (BinaryFractionalCore.decodeState s.state)) =
        expected.map rawFields do throw (IO.userError "guess family raw-field mismatch")
    | _ => throw (IO.userError "raw positive-input branch mismatch")
    IO.println s!"PASS binary full original-input guess family; entries={states.length}; stopping scans=243; operations={r.2}"
  | _ => throw (IO.userError "positive input did not produce its guess family")


end RuntimeGraphCombinedSmoke.Graph
