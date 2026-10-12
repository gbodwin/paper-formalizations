import DirectedFlowCutGap.SupportRecoveryProgram

/-! Proof-only alignment with the existing retained search state. No program
instruction evaluates a proof-carrying path's vertex function. -/
namespace DirectedFlowCutGap.SupportRetainedData
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated BinaryArithmetic

 theorem readEdges_of_mem {V : Type*} [DecidableEq V]
    (xs : List (V×List (V×V))) (unique : (xs.map Prod.fst).Nodup)
    (x : V×List (V×V)) (hx : x∈xs) : (RetainedPathSearch.readEdges x.1 xs).1=x.2 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    have hn := List.nodup_cons.mp unique
    rcases List.mem_cons.mp hx with rfl|hx
    · simp [RetainedPathSearch.readEdges]
    · have hne : y.1≠x.1 := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨x,hx,he.symm⟩)
      simpa [RetainedPathSearch.readEdges,hne] using ih hn.2 hx

 theorem state_codes {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {t : V}
    (S : RetainedPathSearch.State G t) :
    S.codes=S.legacy.entries.map (fun e => (e.1,FlowTable.edgeList e.2)) := by
  have unique : (S.codes.map Prod.fst).Nodup := S.keys_eq.symm ▸ S.legacy.unique
  calc
    S.codes=S.codes.map (fun x => (x.1,(RetainedPathSearch.readEdges x.1 S.codes).1)) := by
      symm
      calc
        _ = S.codes.map id := by
          apply List.map_congr_left
          intro x hx
          change (x.1,(RetainedPathSearch.readEdges x.1 S.codes).1)=x
          rw [readEdges_of_mem S.codes unique x hx]
        _ = S.codes := List.map_id S.codes
    _ = (S.codes.map Prod.fst).map (fun v => (v,(RetainedPathSearch.readEdges v S.codes).1)) := by
      simp only [List.map_map,Function.comp_def]
    _ = (S.legacy.entries.map Sigma.fst).map (fun v => (v,(RetainedPathSearch.readEdges v S.codes).1)) := by
      rw [S.keys_eq]
    _ = S.legacy.entries.map (fun e => (e.1,FlowTable.edgeList e.2)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e he
      change (e.1,(RetainedPathSearch.readEdges e.1 S.codes).1)=(e.1,FlowTable.edgeList e.2)
      rw [S.coherent e he]

 theorem counted_scan_find {α β : Type*} (P : α → Prop) [DecidablePred P]
    (test : CountedSearch.Test P) (f : α → β) (xs : List α) :
    (CountedSearch.scan P test xs).1.map (fun x => f x.1)=(xs.find? (fun x => decide (P x))).map f := by
  rw [CountedSearch.scan_value]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : P x
    · simp [ResidualSearch.scan,List.find?,hx]
    · simpa [ResidualSearch.scan,List.find?,hx,Option.map_map] using ih

end DirectedFlowCutGap.SupportRetainedData
