import MinorFreeSpanners.ClusterGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Literal singleton clusters provide the initial radius-one credit state.
The total initial credit is at most twice the unit-tree budget when the graph
has at least two vertices. The one-vertex case is deliberately not folded into
that inequality. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def singletonClusterBase {V : Type*} (G : SimpleGraph V)
    (w : Sym2 V → ℝ) : ClusterFamily (I:=V) G w 200 where
  branch := fun v => {v}
  nonempty := fun v => ⟨v,rfl⟩
  disjoint := by
    intro i j hij
    exact Set.disjoint_singleton.mpr hij
  connected := by
    intro i x hx y hy
    have hxi : x=i := hx
    have hyi : y=i := hy
    subst x;subst y
    exact ⟨.nil,by simp,by simp [walkWeight]⟩

 theorem singletonClusterBase_cover {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    ∀ x,∃ i,x∈(singletonClusterBase G w).branch i :=
  fun x => ⟨x,rfl⟩

 theorem singletonClusterBase_radius_one {V : Type*} (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (i : V) (x : V) (hx : x∈(singletonClusterBase G w).branch i)
    (y : V) (hy : y∈(singletonClusterBase G w).branch i) :
    ∃ p : G.Walk x y,(∀ z∈p.support,z∈(singletonClusterBase G w).branch i) ∧
      walkWeight w p≤1 := by
  have hxi : x=i := hx
  have hyi : y=i := hy
  subst x;subst y
  exact ⟨.nil,by simp [singletonClusterBase],by simp [walkWeight]⟩

 theorem singleton_initial_credit_le_tree_budget {V : Type*} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) (hsize : 2≤Fintype.card V)
    (c : ℝ) (hc : 0≤c) :
    (∑ _ : V,c)≤2*c*(T.edgeFinset.card:ℝ) := by
  classical
  have he := hT.card_edgeFinset
  have hn : (Fintype.card V:ℝ)≤2*(T.edgeFinset.card:ℝ) := by
    exact_mod_cast (show Fintype.card V≤2*T.edgeFinset.card by omega)
  have hh := mul_le_mul_of_nonneg_right hn hc
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    (show (Fintype.card V:ℝ)*c≤2*c*(T.edgeFinset.card:ℝ) by nlinarith only [hh])

end MinorFreeSpanners
