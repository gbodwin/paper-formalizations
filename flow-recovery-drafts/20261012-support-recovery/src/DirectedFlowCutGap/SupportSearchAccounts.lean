import DirectedFlowCutGap.SupportSearchData

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic

def edgeSteps (e f : Bits × Bits) : ℕ := BinaryComparisonProgram.steps e.1 f.1+
  if same e.1 f.1 then BinaryComparisonProgram.steps e.2 f.2+17 else 9
def edgeCells (e f : Bits × Bits) : ℕ := BinaryComparisonProgram.cells e.1 f.1+2+
  if same e.1 f.1 then BinaryComparisonProgram.cells e.2 f.2 else 0
def memberSteps (e : Bits × Bits) : List (Bits × Bits) → ℕ
  | [] => 3
  | f::fs => edgeSteps f e+(if edgeEq f e then 6 else memberSteps e fs+8)
def memberCells (e : Bits × Bits) : List (Bits × Bits) → ℕ
  | [] => 1
  | f::fs => edgeCells f e+(if edgeEq f e then 0 else memberCells e fs)
def supportSteps (adjacency : List Bits) (es : List (Bits × Bits)) (u v : Bits) : ℕ :=
  GraphAdjacencyProgram.steps u v+
    if GraphRelaxationProgram.adjacent adjacency u v then memberSteps (u,v) es+14 else 10
def supportCells (adjacency : List Bits) (es : List (Bits × Bits)) (u v : Bits) : ℕ :=
  value u+value v+4+
    if GraphRelaxationProgram.adjacent adjacency u v then memberCells (u,v) es else 0
def lookupSteps (u : Bits) : List Code → ℕ
  | [] => 3
  | x::xs => BinaryComparisonProgram.steps x.1 u+(if same x.1 u then 10 else lookupSteps u xs+11)
def lookupCells (u : Bits) : List Code → ℕ
  | [] => 1
  | x::xs => BinaryComparisonProgram.cells x.1 u+(if same x.1 u then 0 else lookupCells u xs)
def predSteps (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) : List Code → ℕ
  | [] => 3
  | x::xs => supportSteps adjacency es u x.1+
      if support adjacency es u x.1 then 12 else predSteps adjacency es u xs+14
def predCells (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) : List Code → ℕ
  | [] => 1
  | x::xs => 2+supportCells adjacency es u x.1+
      if support adjacency es u x.1 then 0 else predCells adjacency es u xs
def visitSteps (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) (xs : List Code) : ℕ :=
  lookupSteps u xs+match lookup u xs with
  | some _ => 8
  | none => predSteps adjacency es u xs+match predecessor adjacency es u xs with
      | none => 16
      | some _ => 23
def visitCells (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) (xs : List Code) : ℕ :=
  1+lookupCells u xs+match lookup u xs with
  | some _ => 0
  | none => 1+predCells adjacency es u xs+match predecessor adjacency es u xs with
      | none => 0
      | some _ => 4
def passSteps (adjacency : List Bits) (es : List (Bits × Bits)) : List Bits → List Code → ℕ
  | [],_ => 3
  | u::us,xs => visitSteps adjacency es u xs+passSteps adjacency es us (visit adjacency es u xs)+11
def passCells (adjacency : List Bits) (es : List (Bits × Bits)) : List Bits → List Code → ℕ
  | [],_ => 0
  | u::us,xs => 2+visitCells adjacency es u xs+passCells adjacency es us (visit adjacency es u xs)
def roundSteps (vs : List Bits) (adjacency : List Bits) (es : List (Bits × Bits)) (target : Bits) : List Bits → ℕ
  | [] => 6
  | _::fuel => roundSteps vs adjacency es target fuel+
      passSteps adjacency es vs (rounds vs adjacency es target fuel)+9
def roundCells (vs : List Bits) (adjacency : List Bits) (es : List (Bits × Bits)) (target : Bits) : List Bits → ℕ
  | [] => 3
  | _::fuel => roundCells vs adjacency es target fuel+1+
      passCells adjacency es vs (rounds vs adjacency es target fuel)
def extractSteps : Option Code → ℕ | none => 2 | some _ => 3
def searchSteps (vs : List Bits) (adjacency : List Bits) (es : List (Bits × Bits)) (source target : Bits) : ℕ :=
  roundSteps vs adjacency es target vs+lookupSteps source (rounds vs adjacency es target vs)+
    extractSteps (lookup source (rounds vs adjacency es target vs))+4
def searchCells (vs : List Bits) (adjacency : List Bits) (es : List (Bits × Bits)) (source target : Bits) : ℕ :=
  roundCells vs adjacency es target vs+lookupCells source (rounds vs adjacency es target vs)

end DirectedFlowCutGap.SupportRecoveryProgram
