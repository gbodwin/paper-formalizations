import DirectedFlowCutGap.ResidualCutFlagsProgram
import DirectedFlowCutGap.ResidualFlowStepProgram
import DirectedFlowCutGap.ResidualCutUniqueness

/-!
# Exact sink-complement flags for the residual network

The stored code table contains precisely the vertices with a simple path
to the sink. Complementing its lookups in numerical vertex order gives the
exact executable minimum cut when the flow is terminal.
-/

namespace DirectedFlowCutGap.ResidualCutData

open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportSearchEncoding SupportRecoveryProgram
open ResidualFlowStepProgram (wordTable pairTable)
open ResidualMatrixProgram (ValueTable)
open ResidualSearchData (pairs)
open ResidualCutFlagsProgram (mark)

def codeTable {n : ℕ} (xs : List (List ResidualRowProgram.Entry)) (label : Fin n → Bits) (t : Fin n) :
    List Code :=
  rounds (wordTable label) (ResidualMatrixProgram.flags xs) (pairTable label) (label t) (wordTable label)

def flags {n : ℕ} (xs : List (List ResidualRowProgram.Entry)) (label : Fin n → Bits) (t : Fin n) : Bits :=
  (wordTable label).map (mark (codeTable xs label t))

private theorem mark_keys {n : ℕ} {G : Digraph (Fin n)} {t : Fin n}
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (S : RetainedPathSearch.State G t) (u : Fin n) :
    mark (encodeCodes label S.codes) (label u)=true ↔ u ∉ ResidualSearch.keys S.legacy.entries := by
  unfold mark
  rw [encode_state_codes,lookup_entries label hlabel,SupportRetainedData.counted_scan_find]
  simp [ResidualSearch.mem_keys]
  constructor
  · intro absent path member
    exact absent ⟨u,path⟩ member rfl
  · intro absent e member equal
    obtain ⟨v,path⟩ := e
    change v=u at equal
    subst v
    exact absent path member

theorem flags_exact {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)} (f : Flow c s t)
    (xs : List (List ResidualRowProgram.Entry)) (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    flags xs label t=(List.finRange n).map
      (fun v => decide (v ∈ finiteResidualCut (ResidualSearch.Enumeration.fin n) f)) := by
  let E := ResidualSearch.Enumeration.fin n
  let A := ResidualSearchData.adjacency f
  let G := FractionalCoverPathOracle.supportGraph (BinaryFractionalWalkOracle.graph A) (pairs n)
  let test := BinaryFractionalWalkOracle.supportTest A (pairs n)
  let S := (RetainedPathSearch.rounds (t:=t) E test (Fintype.card (Fin n))).1
  have sameOrder : E.vertices=List.finRange n := by
    simp [E,ResidualSearch.Enumeration.fin,ResidualSearch.Enumeration.ofEquiv,List.finRange]
    rfl
  have sameCodes : codeTable xs label t=encodeCodes label S.codes := by
    unfold codeTable wordTable pairTable
    rw [← sameOrder,ResidualMatrixProgram.flags_eq f values,← ResidualSearchData.matrix_eq f]
    simpa only [List.length_map,E.length_eq_card,S,A,test] using
      rounds_eq A (pairs n) t label hlabel E (E.vertices.map label)
  have sameTable : S.legacy=(ResidualSearch.searchTable E G t).1 := by
    simpa only [S,ResidualSearch.searchTable] using
      (RetainedPathSearch.rounds_legacy (t:=t) E test _).trans (CountedSearch.rounds_value (t:=t) E test _)
  have graph : G=f.residual := ResidualSearchData.support_eq f
  unfold flags wordTable
  rw [sameCodes,List.map_map]
  apply List.map_congr_left
  intro u _
  apply Bool.eq_iff_iff.mpr
  change mark (encodeCodes label S.codes) (label u)=true ↔ decide (u ∈ finiteResidualCut E f)=true
  rw [mark_keys label hlabel S u,sameTable,ResidualSearch.mem_searchTable_iff,decide_eq_true_eq]
  change ¬Nonempty (SimplePath G u t) ↔ _
  rw [graph,nonempty_simplePath_iff_directedWalk,mem_finiteResidualCut_iff_no_walk]

end DirectedFlowCutGap.ResidualCutData
