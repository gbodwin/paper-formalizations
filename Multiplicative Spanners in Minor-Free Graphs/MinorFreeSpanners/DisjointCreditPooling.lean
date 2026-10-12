import MinorFreeSpanners.VariableConnectorDisjoint

/-! Local inequalities are pooled only after checking disjoint original old
vertex carriers and original connector identities, so neither kind of credit
can be used twice. This is an actual finite host budget, not a quotient count. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
variable {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem disjoint_credit_pooling (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) (hS : ∀ i j,i≠j → Disjoint (S i) (S j))
    (credit : I → ℝ) (cost : J → ℝ) (c : ℝ) (hc : 0≤c)
    (hcredit : ∀ i,0≤credit i) (hw : ∀ e∈T.edgeSet,0≤w e)
    (hpaid : ∀ j,cost j≤(∑ i∈S j,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (H j) (hH j) (S j),w e)) :
    (∑ j,cost j)≤(∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  have hd : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint S := by
    intro i _ j _ hij;exact hS i j hij
  have hvertices : (∑ j,∑ i∈S j,credit i)≤∑ i,credit i := by
    rw [←Finset.sum_biUnion hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hcredit i)
  have hedges := C.connectorEdges_variable_weight_total_le hA hT H hH S hS hw
  have hsum := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset J)) => hpaid j)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  exact hsum.trans (add_le_add hvertices (mul_le_mul_of_nonneg_left hedges hc))

end ClusterFamily
end MinorFreeSpanners
