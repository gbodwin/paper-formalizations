import DirectedFlowCutGap.SupportRetainedVisit

/-! Literal equality with the published forward-updating retained-data search.
These are result equalities; the two implementations' work counters need not agree. -/
namespace DirectedFlowCutGap.SupportSearchEncoding
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportRecoveryProgram

theorem pass_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (es : List (Fin n × Fin n)) {t : Fin n}
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (vs : List (Fin n))
    (S : RetainedPathSearch.State (FractionalCoverPathOracle.supportGraph
      (BinaryFractionalWalkOracle.graph adjacency) es) t) :
    pass (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (vs.map label)
      (encodeCodes label S.codes)=
      encodeCodes label (RetainedPathSearch.pass (BinaryFractionalWalkOracle.supportTest adjacency es) vs S).1.codes := by
  induction vs generalizing S with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons,SupportRecoveryProgram.pass,RetainedPathSearch.pass,visit_eq adjacency es label hlabel,ih]

theorem rounds_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (es : List (Fin n × Fin n)) (t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (E : ResidualSearch.Enumeration (Fin n)) (fuel : List Bits) :
    rounds (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (es.map (encodeEdge label)) (label t) fuel=
      encodeCodes label (RetainedPathSearch.rounds (t:=t) E
        (BinaryFractionalWalkOracle.supportTest adjacency es) fuel.length).1.codes := by
  induction fuel with
  | nil => rfl
  | cons u us ih =>
    simp only [rounds,List.length_cons,RetainedPathSearch.rounds,ih,pass_eq adjacency es label hlabel]

theorem extract_eq {n : ℕ} {G : Digraph (Fin n)} [DecidableRel G.Adj] {t : Fin n}
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (s : Fin n)
    (S : RetainedPathSearch.State G t)
    (complete : ∀ u,SimplePath G u t → u∈ResidualSearch.keys S.legacy.entries) :
    (match lookup (label s) (encodeCodes label S.codes) with
      | none => [] | some x => x.2)=
      (RetainedPathSearch.extract S complete s).edges.map (encodeEdge label) := by
  have hl := lookup_entries label hlabel s S.legacy.entries
  rw [←encode_state_codes label S] at hl
  cases he : (CountedSearch.scan (fun e : ResidualSearch.Entry G t => e.1=s)
      (fun e => (inferInstanceAs (Decidable (e.1=s)),1)) S.legacy.entries).1 with
  | none =>
    simp only [hl,he,Option.map_none]
    unfold RetainedPathSearch.extract
    dsimp only
    split
    · rename_i e hh
      cases he.symm.trans hh
    · rfl
  | some e =>
    have hc : (RetainedPathSearch.readEdges s S.codes).1=FlowTable.edgeList e.1.2 :=
      (congrArg (fun v => (RetainedPathSearch.readEdges v S.codes).1) e.2.2.symm).trans
        (S.coherent e.1 e.2.1)
    simp only [hl,he,Option.map_some,encodeEntry,encodeCode]
    unfold RetainedPathSearch.extract
    dsimp only
    split
    · dsimp only
      rw [hc]
    · rename_i hh
      cases he.symm.trans hh

theorem lookup_same_value (u v : Bits) (h : value u=value v) (xs : List Code) :
    lookup u xs=lookup v xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [lookup,same,GraphDiscoveryProgram.order_eq,h,ih]

theorem search_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (es : List (Fin n × Fin n)) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (E : ResidualSearch.Enumeration (Fin n)) (sw : Bits) (hsw : value sw=s.val) :
    search (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (es.map (encodeEdge label)) sw (label t)=
      (RetainedPathSearch.search E (BinaryFractionalWalkOracle.supportTest adjacency es) s t).edges.map
        (encodeEdge label) := by
  unfold search
  rw [rounds_eq adjacency es t label hlabel]
  simp only [List.length_map,E.length_eq_card]
  rw [lookup_same_value sw (label s) (hsw.trans (hlabel s).symm)]
  exact extract_eq label hlabel s _ _

end DirectedFlowCutGap.SupportSearchEncoding
