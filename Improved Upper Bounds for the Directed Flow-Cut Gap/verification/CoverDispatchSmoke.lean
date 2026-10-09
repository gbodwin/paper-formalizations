import DirectedFlowCutGap.FractionalCoverGuesses
open DirectedFlowCutGap
open IntegralNetworkFlow FractionalCover

namespace FractionalCoverDispatchRawSmoke

def emptyInput : FractionalCoverGraphOracle.Input 0 where
  adjacency := #v[]
  demands := []
  costs := #v[]

def directInput : FractionalCoverGraphOracle.Input 2 where
  adjacency := #v[#v[false,true],#v[false,false]]
  demands := [(0,1)]
  costs := #v[1,0]

def disconnectedInput : FractionalCoverGraphOracle.Input 2 where
  adjacency := #v[#v[false,false],#v[false,false]]
  demands := [(0,1)]
  costs := #v[1,1]

def freeInput : FractionalCoverGraphOracle.Input 3 where
  adjacency := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  demands := [(0,2)]
  costs := #v[0,0,1]

def endpointsFreeInput : FractionalCoverGraphOracle.Input 3 where
  adjacency := freeInput.adjacency
  demands := [(0,2)]
  costs := #v[0,1,0]

def mixedInput : FractionalCoverGraphOracle.Input 4 where
  adjacency := #v[#v[false,true,true,false],#v[false,false,false,true],
    #v[false,false,false,true],#v[false,false,false,false]]
  demands := [(0,3)]
  costs := #v[1,0,4,1]

#eval do
  match FractionalCoverGuesses.runInput emptyInput 0 with
  | .zero X => if !(decide (X=∅)) then throw (IO.userError "zero-vertex cut was nonempty")
  | _ => throw (IO.userError "zero-vertex dispatch failed")
  match FractionalCoverGuesses.runInput directInput 1 with
  | .infeasible d => if d != (0,1) then throw (IO.userError "wrong empty-column witness")
  | _ => throw (IO.userError "direct demand did not report infeasibility")
  match FractionalCoverGuesses.runInput disconnectedInput 1 with
  | .zero X => if !(decide (X=∅)) then throw (IO.userError "unreachable graph returned a nonempty cut")
  | _ => throw (IO.userError "unreachable dispatch failed")
  match FractionalCoverGuesses.runInput freeInput 1 with
  | .zero X =>
    if !(1 ∈ X) then throw (IO.userError "free internal resource not selected")
  | _ => throw (IO.userError "zero-cost cut was not returned")
  match FractionalCoverGuesses.runInput {directInput with demands := [(0,0)]} 1 with
  | .infeasible d => if d != (0,0) then throw (IO.userError "wrong diagonal witness")
  | _ => throw (IO.userError "diagonal demand did not report infeasibility")
  match FractionalCoverDispatch.dispatch endpointsFreeInput.graph endpointsFreeInput.demands
      endpointsFreeInput.costs with
  | .positive q =>
    if q.path.edges != [(0,1),(1,2)] then throw (IO.userError "wrong endpoint-preserving path")
  | _ => throw (IO.userError "zero-cost demand endpoints were incorrectly deleted")
  IO.println "PASS: zero vertices, empty demand family, infeasible direct/diagonal demands, unreachable demand, free internal cut, and a surviving path through zero-cost demand endpoints"
  match FractionalCoverGuesses.runInput mixedInput 3 with
  | .covers states =>
    if states.length != 15 then throw (IO.userError "wrong explicit doubling-grid length")
    if !(states.all fun s => decide (1 ≤ value s.best 1 ∧ 1 ≤ value s.best 2)) then
      throw (IO.userError "an actual lambda output is infeasible")
    if !(states.any fun s => decide (objective mixedInput.costs s.best ≤ 24 ∧
        (value s.best 0+value s.best 1+value s.best 2+value s.best 3) ≤ 24)) then
      throw (IO.userError "no jointly bounded guess against cost-four mass-two cover")
    IO.println s!"PASS: {states.length} actual c+lambda graph solves, every returned cover feasible, a jointly cost-six/mass-twelve entry present"
  | _ => throw (IO.userError "mixed zero/positive input did not produce guesses")

end FractionalCoverDispatchRawSmoke
