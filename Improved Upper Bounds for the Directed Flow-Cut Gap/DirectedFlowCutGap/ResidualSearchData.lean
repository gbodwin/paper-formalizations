import DirectedFlowCutGap.ResidualMatrixProgram
import DirectedFlowCutGap.ActualSupportSearch
import DirectedFlowCutGap.RetainedMassTableProgram

/-!
# Exact residual path data

The retained graph-search program checks both matrix adjacency and membership
in its support list. The complete ordered pair list makes the support test
equivalent to matrix adjacency. Thus the same program can search a signed-flow
residual matrix directly, with the original retained predecessor order.
-/

namespace DirectedFlowCutGap.ResidualSearchData

open IntegralNetworkFlow IntegralNetworkFlow.Tabulated BinaryArithmetic
open BinaryFractionalWalkOracle (Adjacency)
open SupportSearchEncoding (encodeEdge)

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

def adjacency (f : Flow c s t) : Adjacency n :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => decide (f.amount u v < (c u v : ℤ))))

theorem matrix_eq (f : Flow c s t) :
    GraphRelaxationRefinement.matrix (adjacency f) =
      ResidualMatrixProgram.residualFlags f (List.finRange n) (List.finRange n) := by
  simp only [GraphRelaxationRefinement.matrix,adjacency,ResidualMatrixProgram.residualFlags,
    Vector.toList_ofFn,List.finRange,List.map_ofFn,Function.comp_def]

abbrev pairs (n : ℕ) := RetainedMassTableProgram.pairOrder n

theorem pair_count (n : ℕ) : (pairs n).length=n*n := by
  exact (List.length_product (List.finRange n) (List.finRange n)).trans (by simp)

theorem support_eq (f : Flow c s t) :
    FractionalCoverPathOracle.supportGraph (BinaryFractionalWalkOracle.graph (adjacency f))
      (pairs n) = f.residual := by
  apply Digraph.ext
  funext u v
  apply propext
  simp [FractionalCoverPathOracle.supportGraph,EncodedIntegerShortestPaths.graph,adjacency,
    RetainedMassTableProgram.pairOrder,Flow.residual]

def PathResult (f : Flow c s t) (label : Fin n → Bits) (es : List (Bits×Bits)) : Prop :=
  (es=[] ∧ ¬Nonempty (SimplePath f.residual s t)) ∨
    (∃ p : SimplePath f.residual s t,es=(FlowTable.edgeList p).map (encodeEdge label) ∧ es≠[])

private theorem search_certificate {G D : Digraph (Fin n)} (hG : G=D)
    (r : RetainedPathSearch.Result G s t) (label : Fin n → Bits) (different : s≠t) :
    ((r.edges.map (encodeEdge label))=[] ∧ ¬Nonempty (SimplePath D s t)) ∨
      (∃ p : SimplePath D s t,r.edges.map (encodeEdge label)=
        (FlowTable.edgeList p).map (encodeEdge label) ∧ (r.edges.map (encodeEdge label))≠[]) := by
  subst D
  cases h : r.result with
  | stopped hp =>
    have empty : r.edges=[] := by simpa only [h] using r.correct
    exact Or.inl ⟨by simp [empty],hp⟩
  | found p =>
    have exactEdges : r.edges=FlowTable.edgeList p := by simpa only [h] using r.correct
    have length : p.edgeLength≠0 := by
      intro zero
      apply different
      have endpoints : (0 : Fin (p.edgeLength+1))=Fin.last p.edgeLength := by
        apply Fin.ext
        simpa only [Fin.val_zero,Fin.val_last] using zero.symm
      exact p.source_eq.symm.trans ((congrArg p.vertex endpoints).trans p.target_eq)
    refine Or.inr ⟨p,congrArg (List.map (encodeEdge label)) exactEdges,?_⟩
    intro empty
    have leneq := congrArg List.length empty
    simp only [List.length_map,List.length_nil,exactEdges,FlowTable.edgeList_length] at leneq
    exact length leneq

theorem result_exact (f : Flow c s t) (different : s≠t) (E : ResidualSearch.Enumeration (Fin n))
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (source : Bits) (hsource : value source=s.val) :
    PathResult f label (SupportRecoveryProgram.search (E.vertices.map label)
      (ResidualMatrixProgram.residualFlags f (List.finRange n) (List.finRange n))
      ((pairs n).map (encodeEdge label)) source (label t)) := by
  rw [← matrix_eq f,SupportSearchEncoding.search_eq _ _ s t label hlabel E source hsource]
  exact search_certificate (support_eq f) _ label different

end DirectedFlowCutGap.ResidualSearchData
