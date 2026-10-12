import DirectedFlowCutGap.SupportRetainedSearch
import DirectedFlowCutGap.SupportIterationBounds
import DirectedFlowCutGap.SupportSearchLowerMachine

/-! The actual lower-machine support search returns the literal old retained
search's edge list. Padded labels, the represented matrix and support list,
and the initial heap/word-width bounds remain explicit inputs. -/
namespace DirectedFlowCutGap.SupportSearchEncoding
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open GraphWalkExtension SupportRecoveryProgram

theorem complete_mono (C H A i j : ℕ) (h : i ≤ j) :
    completeBound C H A i ≤ completeBound C H A j := by
  unfold completeBound runBound stepBound
  gcongr

theorem graph_bit {n H A : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (s t : Fin n)
    (sw : Bits) (hsw : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (initial : BitState 280) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=270) (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Vertices (eraseState initial).heap (eraseState initial).registers.a (E.vertices.map label))
    (context : StoredGlobalContext (eraseState initial).heap (eraseState initial).registers.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label t))
    (word : BoolList (eraseState initial).heap (eraseState initial).registers.c sw)
    (W : ℕ) (hw : sw.length ≤ W) (labels : ∀ i,(label i).length ≤ W) :
    ∃ steps charge out,Run SupportRecoveryProgram.program steps charge initial [] out ∧
      steps ≤ searchCap n es.length W n+1 ∧
      EdgeList (eraseState out).heap (eraseState out).registers.d
        ((RetainedPathSearch.search E (BinaryFractionalWalkOracle.supportTest adjacency es) s t).edges.map
          (encodeEdge label)) ∧
      Vertices (eraseState out).heap (eraseState initial).registers.a (E.vertices.map label) ∧
      StoredGlobalContext (eraseState out).heap (eraseState initial).registers.b
        (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label t) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c sw ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=279 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=searchCells (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
          (es.map (encodeEdge label)) sw (label t)) ∧
      (attempt SupportRecoveryProgram.program out).result=none ∧
      charge+(attempt SupportRecoveryProgram.program out).operations ≤
        completeBound 280 H A (searchCap n es.length W n+1) := by
  have rows : n ≤ (GraphRelaxationRefinement.matrix adjacency).length := by
    simp [GraphRelaxationRefinement.matrix_length]
  have cols : ∀ (i : ℕ) (hi : i<n),
      n ≤ ((GraphRelaxationRefinement.matrix adjacency)[i]'(lt_of_lt_of_le hi rows)).length := by
    intro i hi
    exact (GraphRelaxationRefinement.matrix_row_length adjacency ⟨i,hi⟩).ge
  have hv : ∀ u∈E.vertices.map label,value u<n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel]
    exact i.isLt
  have ht : value (label t)<n := by rw [hlabel];exact t.isLt
  have hwords : ∀ u∈E.vertices.map label,WordBound W n u := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    exact ⟨labels i,by rw [hlabel];exact i.isLt.le⟩
  have htarget : WordBound W n (label t) := ⟨labels t,ht.le⟩
  have hedges : ∀ e∈es.map (encodeEdge label),EdgeWidths W e := by
    intro e he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    exact ⟨labels x.1,labels x.2⟩
  have hsteps := search_steps_le W n (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
    (es.map (encodeEdge label)) sw (label t) hwords htarget hw hedges
  simp only [List.length_map,E.length_eq_card,Fintype.card_fin] at hsteps
  obtain ⟨charge,out,run,rep,keepV,keepC,keepW,src,stack,pc,heap,halt,price⟩ :=
    search_bit n initial bounded pc0 hn empty input context word rows cols hv ht
  refine ⟨_,charge,out,run,Nat.add_le_add_right hsteps 1,?_,keepV,keepC,keepW,src,stack,pc,heap,halt,?_⟩
  · simpa only [search_eq adjacency es s t label hlabel E sw hsw] using rep
  · exact price.trans (complete_mono 280 H A _ _ (Nat.add_le_add_right hsteps 1))

end DirectedFlowCutGap.SupportSearchEncoding
