import DirectedFlowCutGap.DemandCollectionRefinement
import DirectedFlowCutGap.DemandCollectionSelection
import DirectedFlowCutGap.CostedCandidateBounds

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open GraphWalkExtension

def instructionBound (k n W : ℕ) : ℕ :=
  k*(GraphRecoveryController.instructionBound n W W+37)+
    (6400*(n*(W+1)+2)^2+12)*k+10

theorem records_length (vs adjacency : List Bits) (rows : List Fraction) (next : ℕ) (xs : List Demand) :
    (records vs adjacency rows next xs).length≤xs.length := by
  induction xs with
  | nil => simp [records]
  | cons x xs ih =>
    cases hq : query vs adjacency rows x <;> simp only [records,hq,List.length_cons] <;> omega

theorem collection_steps_le {vs adjacency : List Bits} {rows : List Fraction} (xs : List Demand) (Q : ℕ)
    (bound : ∀ x∈xs,querySteps vs adjacency rows x≤Q) : steps vs adjacency rows xs≤xs.length*(Q+37)+3 := by
  induction xs with
  | nil => simp [steps]
  | cons x xs ih =>
    have hx := bound x List.mem_cons_self
    have ht := ih (fun y hy => bound y (List.mem_cons_of_mem _ hy))
    cases hq : query vs adjacency rows x <;> simp only [steps,hq,List.length_cons] <;> nlinarith

theorem record_widths {vs adjacency : List Bits} {rows : List Fraction} (next : ℕ) (xs : List Demand) (W : ℕ)
    (bound : ∀ x∈xs,∀ q,query vs adjacency rows x=some q → StoredBounded q.cost W) :
    ∀ z∈records vs adjacency rows next xs,RetainedArgminProgram.Fits W z.item := by
  induction xs with
  | nil => simp [records]
  | cons x xs ih =>
    have ht := ih (fun y hy => bound y (List.mem_cons_of_mem _ hy))
    cases hq : query vs adjacency rows x with
    | none => simpa only [records,hq] using ht
    | some q =>
      intro z hz
      simp only [records,hq,List.mem_cons] at hz
      rcases hz with rfl|hz
      · exact bound x List.mem_cons_self q hq
      · exact ht z hz

theorem query_cost_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t : Fin n) (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W)
    (rowWidths : ∀ q∈y.toList,StoredBounded q W) (q : Walk)
    (chosen : GraphRecoveryController.result ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList (label s) (label t) (label s)=some q) :
    StoredBounded q.cost (n*(W+1)+1) := by
  let E := ResidualSearch.Enumeration.fin n
  have hm := GraphDiscoveryRefinement.minimize_eq E adjacency y s t (label s) (hlabel s) label hlabel
  change GraphDiscoveryProgram.minimize _ _ _ _ _ _=_ at hm
  unfold GraphRecoveryController.result at chosen
  rw [hm] at chosen
  cases ho : (BinaryFractionalWalkOracle.minimize E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1 with
  | none => simp [ho] at chosen
  | some old =>
    simp only [ho,Option.map_some,Option.some.injEq] at chosen
    subst q
    have len := CostedSupportProgram.recovered_length E adjacency old.edges s t (label s) (hlabel s) label hlabel
    have words := CostedSupportProgram.recovered_words E adjacency old.edges s t (label s) (hlabel s) label hlabel W labels
    let x : CostedCandidateMaterialization.Candidate :=
      ⟨(CostedSupportProgram.edges (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
        (old.edges.map (SupportSearchEncoding.encodeEdge label)) (label s) (label t)).map Prod.fst,label s,0⟩
    have hbound : CostedCandidateBounds.InputBound W n x := by
      exact ⟨by simpa [x] using len,labels s,fun w hw => (words w hw).1⟩
    have valid : ∀ w∈x.words,value w<y.toList.length := by
      intro w hw
      simpa only [Vector.length_toList] using (words w hw).2
    exact CostedCandidateBounds.score_width y.toList x n W hW rowWidths hbound valid

theorem graph_queries_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (W : ℕ) (hW : 1≤W)
    (labels : ∀ i,(label i).length≤W) (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    (∀ x∈xs,querySteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList x≤GraphRecoveryController.instructionBound n W W) ∧
    (∀ x∈xs,∀ q,query ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList x=some q → StoredBounded q.cost (n*(W+1)+1)) := by
  constructor
  · intro x hx
    obtain ⟨d,_,hd⟩ := encoded_demand_witness label encoded x hx
    have hp := GraphRecoveryController.steps_bound (ResidualSearch.Enumeration.fin n) adjacency y d.1 d.2
      (label d.1) (hlabel d.1) label hlabel W hW (labels d.1) labels rowWidths
    have mono : GraphRecoveryController.instructionBound n W (label d.1).length≤
        GraphRecoveryController.instructionBound n W W := by
      unfold GraphRecoveryController.instructionBound GraphDiscoveryProgram.discoveryBudget
        GraphDiscoveryProgram.roundBudget GraphDiscoveryProgram.passBudget
        GraphRelaxationProgram.instructionBound GraphRelaxationProgram.perEntryBound
      gcongr
      exact labels d.1
    have hh := hp.trans mono
    unfold querySteps
    rw [hd.1,hd.2]
    omega
  · intro x hx q hq
    obtain ⟨d,_,hd⟩ := encoded_demand_witness label encoded x hx
    apply query_cost_bound adjacency y label hlabel d.1 d.2 W hW labels rowWidths q
    simpa only [query,hd.1,hd.2] using hq

theorem graph_steps_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (next W : ℕ) (hW : 1≤W)
    (labels : ∀ i,(label i).length≤W) (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList next xs≤ instructionBound xs.length n W := by
  obtain ⟨queries,widths⟩ := graph_queries_bound adjacency y label hlabel encoded W hW labels rowWidths
  have hc := collection_steps_le xs (GraphRecoveryController.instructionBound n W W) queries
  have hw := record_widths next xs (n*(W+1)+1) widths
  have hs := RetainedArgminProgram.steps_bound
    ((records ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList next xs).map Record.item) (M:=n*(W+1)+1) (by
        intro z hz
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
        exact hw q hq)
  simp only [List.length_map, Nat.add_assoc, show (1:ℕ)+1=2 from rfl] at hs
  have len := records_length ((ResidualSearch.Enumeration.fin n).vertices.map label)
    (GraphRelaxationRefinement.matrix adjacency) y.toList next xs
  have mono := Nat.mul_le_mul_left (6400*(n*(W+1)+2)^2+12) len
  simp only [selectedSteps,instructionBound]
  omega

end DirectedFlowCutGap.DemandCollection
