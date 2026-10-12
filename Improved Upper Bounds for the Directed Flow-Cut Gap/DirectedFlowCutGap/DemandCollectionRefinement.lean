import DirectedFlowCutGap.DemandCollectionExecution
import DirectedFlowCutGap.GraphRecoveryRefinement

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open GraphWalkExtension

def EncodesDemand {n : ℕ} (label : Fin n → Bits) (x : Demand)
    (d : BinaryFractionalWalkOracle.Pair n) : Prop :=
  x.sourceWord=label d.1 ∧ x.targetWord=label d.2

def EncodesRecord {n : ℕ} (label : Fin n → Bits) (z : Record)
    (q : BinaryFractionalGraphOracle.Selected n) : Prop :=
  EncodesDemand label z.demand q.demand ∧
    z.path=GraphRelaxationRefinement.encode label q.path ∧ z.item.score=q.path.cost

theorem encoded_demand_witness {n : ℕ} (label : Fin n → Bits)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) :
    ∀ x∈xs,∃ d∈ds,EncodesDemand label x d := by
  induction encoded with
  | nil => simp
  | cons hd _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨_,List.mem_cons_self,hd⟩
    · obtain ⟨d,hd',he⟩ := ih x hx
      exact ⟨d,List.mem_cons_of_mem _ hd',he⟩

theorem encoded_query_valid {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) :
    ∀ x∈xs,value x.targetWord<n ∧
      ∀ q,GraphDiscoveryProgram.minimize ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList x.sourceWord x.targetWord x.sourceWord=some q →
        ∀ w∈(CostedSupportProgram.edges ((ResidualSearch.Enumeration.fin n).vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) q.edges x.sourceWord x.targetWord).map Prod.fst,
          value w<y.toList.length := by
  intro x hx
  obtain ⟨d,_,hd⟩ := encoded_demand_witness label encoded x hx
  rw [hd.1,hd.2]
  exact ⟨by rw [hlabel];exact d.2.isLt,
    GraphRecoveryController.recovery_valid (ResidualSearch.Enumeration.fin n) adjacency y d.1 d.2
      (label d.1) (hlabel d.1) label hlabel⟩

/-- Every successful actual query contributes its original demand and exact old
shortest path in the original list order. Absent results contribute no record. -/
theorem records_refine {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (next : ℕ) :
    List.Forall₂ (EncodesRecord label)
      (records ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList next xs)
      (BinaryFractionalGraphOracle.collect adjacency y ds).1 := by
  induction encoded with
  | nil => exact .nil
  | @cons x d xs ds hd htail ih =>
    have eqQuery : query ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList x=
        (BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n) adjacency
          (BinaryFractionalGraphOracle.outgoing y d.1) d.1 d.2).1.map
            (GraphRelaxationRefinement.encode label) := by
      simpa only [query,hd.1,hd.2] using GraphRecoveryController.result_eq
        (ResidualSearch.Enumeration.fin n) adjacency y d.1 d.2 (label d.1) (hlabel d.1) label hlabel
    cases hq : (BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n) adjacency
        (BinaryFractionalGraphOracle.outgoing y d.1) d.1 d.2).1 with
    | none =>
      simpa only [records,BinaryFractionalGraphOracle.collect,eqQuery,hq,Option.map_none] using ih
    | some q =>
      simp only [records,BinaryFractionalGraphOracle.collect,eqQuery,hq,Option.map_some]
      exact .cons ⟨hd,rfl,rfl⟩ ih

theorem records_score {vs adjacency : List Bits} {rows : List Fraction} (next : ℕ) (xs : List Demand) :
    ∀ z∈records vs adjacency rows next xs,z.item.score=z.path.cost := by
  induction xs with
  | nil => simp [records]
  | cons x xs ih =>
    cases hq : query vs adjacency rows x with
    | none => simpa only [records,hq] using ih
    | some q =>
      intro z hz
      simp only [records,hq,List.mem_cons] at hz
      rcases hz with rfl|hz
      · rfl
      · exact ih z hz

end DirectedFlowCutGap.DemandCollection
