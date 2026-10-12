import DirectedFlowCutGap.GraphBoundedRounds
import DirectedFlowCutGap.GraphLookupCalls

/-! The newly built table is the literal frozen binary oracle table, including
padded labels, canonical fractions, vertex order and target-zero behavior. -/
namespace DirectedFlowCutGap.GraphDiscoveryRefinement
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension
open GraphDiscoveryProgram GraphRelaxationRefinement IntegralNetworkFlow

theorem zero_encode {n : ℕ} (label : Fin n → Bits) :
    GraphDiscoveryProgram.zero=encode label BinaryFractionalWalkOracle.zero := rfl

theorem atVertex_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u : Fin n)
    (old : BinaryFractionalWalkOracle.Table n) :
    atVertex (matrix adjacency) y.toList sw (label t) (label u) (encodeTable label old)=
      (BinaryFractionalWalkOracle.atVertex adjacency (BinaryFractionalGraphOracle.outgoing y s) t u old).1.map
        (encode label) := by
  have he : BinaryComparisonProgram.order (label u) (label t)=.eq ↔ u=t := by
    rw [order_eq,hlabel,hlabel]
    exact Fin.ext_iff.symm
  by_cases h : u=t
  · rw [GraphDiscoveryProgram.atVertex]
    simp only [he.mpr h,ite_true]
    simp only [BinaryFractionalWalkOracle.atVertex,h,ite_true,Option.map_some]
    rfl
  · simp only [atVertex,BinaryFractionalWalkOracle.atVertex,h,ite_false,he]
    exact scan_eq adjacency y s sw hs label hlabel u old

theorem pass_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (old : BinaryFractionalWalkOracle.Table n) (vertices : List (Fin n)) :
    pass (matrix adjacency) y.toList sw (label t) (encodeTable label old) (vertices.map label)=
      encodeTable label (BinaryFractionalWalkOracle.pass adjacency (BinaryFractionalGraphOracle.outgoing y s) t old vertices).1 := by
  induction vertices with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons,GraphDiscoveryProgram.pass,BinaryFractionalWalkOracle.pass]
    rw [atVertex_eq adjacency y s t sw hs label hlabel u old]
    cases (BinaryFractionalWalkOracle.atVertex adjacency (BinaryFractionalGraphOracle.outgoing y s) t u old).1 <;>
      simp_all [encodeTable]

theorem rounds_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (s t : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (vertices fuel : List (Fin n)) :
    rounds (vertices.map label) (matrix adjacency) y.toList sw (label t) (fuel.map label)=
      encodeTable label (BinaryFractionalWalkOracle.rounds vertices adjacency (BinaryFractionalGraphOracle.outgoing y s) t fuel).1 := by
  induction fuel with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons,rounds,BinaryFractionalWalkOracle.rounds]
    rw [ih,pass_eq adjacency y s t sw hs label hlabel]


theorem lookup_eq {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (u : Fin n) (xs : BinaryFractionalWalkOracle.Table n) :
    GraphDiscoveryProgram.lookup (label u) (encodeTable label xs)=
      (BinaryFractionalWalkOracle.lookup u xs).1.map (encode label) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨v,q⟩
    have he : BinaryComparisonProgram.order (label v) (label u)=.eq ↔ u=v := by
      rw [order_eq,hlabel,hlabel]
      exact ⟨fun h => Fin.ext h.symm,fun h => congrArg Fin.val h.symm⟩
    simp only [encodeTable,List.map_cons,GraphDiscoveryProgram.lookup,BinaryFractionalWalkOracle.lookup]
    simp only [he]
    split
    · rw [show GraphDiscoveryProgram.lookup (label u)
        (List.map (fun x => (label x.1,encode label x.2)) xs)=_ from ih,pick_eq]
    · exact ih

theorem minimize_eq {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    GraphDiscoveryProgram.lookup (label s)
      (rounds (E.vertices.map label) (matrix adjacency) y.toList sw (label t) (E.vertices.map label))=
      (BinaryFractionalWalkOracle.minimize E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1.map
        (encode label) := by
  rw [rounds_eq adjacency y s t sw hs label hlabel,lookup_eq label hlabel]
  rfl

end DirectedFlowCutGap.GraphDiscoveryRefinement
