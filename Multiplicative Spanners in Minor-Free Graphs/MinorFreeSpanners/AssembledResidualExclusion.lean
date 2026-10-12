import MinorFreeSpanners.AssembledPathFamilies
import MinorFreeSpanners.ResidualUnpaidLabels

/-! Residual heavy-edge exclusion uses the exact globally assembled component
blocks, selected donors and endpoint sets from the weighted root construction.
No second existential segmentation is chosen for classification. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] {A T B G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) A w D₀} {hA : A≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare future : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hA hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port (fun i => d i+1) credit M L c b a (spare r) (future r) N)

noncomputable def paidLabels : Finset I := by
  classical
  exact residualStepOneLabels Finset.univ (blocks O Q) (selected O Q) (ends O Q) N

 theorem exact_residual_cover :
    Finset.univ.biUnion (ResidualComponents.block H (Finset.univ\roots))=Finset.univ\roots := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨t,_,hi⟩ := Finset.mem_biUnion.mp hi
    exact ResidualComponents.subset H _ t hi
  · intro hi
    obtain ⟨t,ht⟩ := ResidualComponents.covers H (Finset.univ\roots) hi
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,ht⟩

 theorem no_unpaid_edge (hforest : H.IsAcyclic) (W U : Finset I)
    (hRW : Finset.univ\roots⊆W) (hRU : Disjoint (Finset.univ\roots) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (hL : 0<L) (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D₀) :
    ∀ i∈Finset.univ\roots,∀ j∈Finset.univ\roots,i∉paidLabels O Q → j∉paidLabels O Q →
      ∀ x∈C.branch i,∀ y∈C.branch j,¬B.Adj x y := by
  classical
  intro i hi j hj hip hjp x hx y hy
  have hi' : i∈Finset.univ.biUnion (ResidualComponents.block H (Finset.univ\roots)) := by
    rw [exact_residual_cover];exact hi
  have hj' : j∈Finset.univ.biUnion (ResidualComponents.block H (Finset.univ\roots)) := by
    rw [exact_residual_cover];exact hj
  exact C.no_unpaid_residual_edge H hforest d L M W U (Finset.univ\roots) hRW hRU hmax
    Finset.univ N O.port (blocks O Q) (selected O Q) (ends O Q)
    (fun t _ => component_partition O Q t) hL hd0 hd hi' hj' hip hjp hx hy

 theorem old_label_cover (i : I) : i∈Finset.univ\roots ∨ i∈paidLabels O Q ∨ i∈roots := by
  classical
  by_cases hi : i∈roots
  · exact Or.inr (Or.inr hi)
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩)

end AssembledPathFamilies
end MinorFreeSpanners
