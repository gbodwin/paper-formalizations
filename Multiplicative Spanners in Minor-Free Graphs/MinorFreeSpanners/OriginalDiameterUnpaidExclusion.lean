import MinorFreeSpanners.OriginalDiameterInteriorExclusion
import MinorFreeSpanners.AssembledResidualExclusion

/-! The exact unpaid labels of the existing multi-root path assembly exclude
original heavy edges by the original small-cluster maximality. All blocks,
selected donors and endpoint sets remain those already used by its ledger. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem no_original_diameter_mixed_unpaid_edge (C : ClusterFamily (I:=I) A w D)
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hK : K.IsAcyclic) (hH : H.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ) (L M : ℝ) (W U : Finset I)
    (hRW : Finset.univ\P.biUnion id⊆W) (hRU : Disjoint (Finset.univ\P.biUnion id) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (N : ℕ)
    (port : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent → SelectedResidualIndex P)
    (blocks : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent → Finset (Finset (SelectedResidualIndex P)))
    (selected ends : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent → Finset (SelectedResidualIndex P))
    (hpart : ∀ t,ResidualAttachmentPartition K (Finset.univ\selectedRoots P) t
      (mixedEffectiveDiameter d radius) M L N (port t) (blocks t) (selected t) (ends t))
    (hL : 0<L) (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D)
    {x y : {i // i∉P.biUnion id}}
    (hxpaid : Sum.inr x∉residualStepOneLabels Finset.univ blocks selected ends N)
    (hypaid : Sum.inr y∉residualStepOneLabels Finset.univ blocks selected ends N)
    {a b : V} (ha : a∈C.branch x.val) (hb : b∈C.branch y.val) : ¬B.Adj a b := by
  classical
  have hx : Sum.inr x∈Finset.univ.biUnion (ResidualComponents.block K (Finset.univ\selectedRoots P)) := by
    rw [AssembledPathFamilies.exact_residual_cover]
    simp [selectedRoots]
  have hy : Sum.inr y∈Finset.univ.biUnion (ResidualComponents.block K (Finset.univ\selectedRoots P)) := by
    rw [AssembledPathFamilies.exact_residual_cover]
    simp [selectedRoots]
  obtain ⟨t,_,S,hS,hSN,hxS,hxE⟩ := unpaid_residual_label_block K _ Finset.univ
    (mixedEffectiveDiameter d radius) M L N port blocks selected ends (fun t _ => hpart t) hx hxpaid
  obtain ⟨q,_,T,hT,hTN,hyT,hyE⟩ := unpaid_residual_label_block K _ Finset.univ
    (mixedEffectiveDiameter d radius) M L N port blocks selected ends (fun t _ => hpart t) hy hypaid
  exact C.no_original_diameter_mixed_interior_edge P K H hK hH hres d radius L M W U hRW hRU hmax
    N port blocks selected ends hpart hL hd0 hd hS hT hSN hTN hxS hyT hxE hyE ha hb

end ClusterFamily
end MinorFreeSpanners
