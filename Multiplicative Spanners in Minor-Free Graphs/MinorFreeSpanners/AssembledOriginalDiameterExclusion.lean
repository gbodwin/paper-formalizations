import MinorFreeSpanners.OriginalDiameterUnpaidExclusion

/-! The original-diameter exclusion applies to precisely the component
partitions of the existing weighted root-fiber assembly, without selecting a
second family of blocks or assuming maximality at the enlarged root diameter. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem no_unpaid_edge_original_diameter
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) {hT : T≤G}
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (K : SimpleGraph (SelectedResidualIndex P)) {hKsub : K≤(C.selectedResidual hA P F hbranch).graph T}
    (H : SimpleGraph I) (hK : K.IsAcyclic) (hH : H.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ)
    (mixed credit : SelectedResidualIndex P → ℝ) (hmixed : (fun i => mixed i+1)=mixedEffectiveDiameter d radius)
    (M L c b a : ℝ) (spare reserve : {r // r∈selectedRoots P} → ℝ) (N : ℕ)
    (O : ResidualOwnership K (selectedRoots P))
    (Q : (r : {r // r∈selectedRoots P}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch)
      le_rfl hT K hKsub (Finset.univ\selectedRoots P) r.val (O.components r) O.port
      (fun i => mixed i+1) credit M L c b a (spare r) (reserve r) N)
    (W U : Finset I) (hRW : Finset.univ\P.biUnion id⊆W) (hRU : Disjoint (Finset.univ\P.biUnion id) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (hL : 0<L) (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D) :
    ∀ i∈Finset.univ\selectedRoots P,∀ j∈Finset.univ\selectedRoots P,
      i∉paidLabels O Q → j∉paidLabels O Q →
      ∀ x∈(C.selectedResidual hA P F hbranch).branch i,
        ∀ y∈(C.selectedResidual hA P F hbranch).branch j,¬B.Adj x y := by
  classical
  intro i hi j hj hip hjp x hx y hy
  cases i with
  | inl S => exact ((Finset.mem_sdiff.mp hi).2 (by simp [selectedRoots])).elim
  | inr i =>
    cases j with
    | inl S => exact ((Finset.mem_sdiff.mp hj).2 (by simp [selectedRoots])).elim
    | inr j =>
      exact C.no_original_diameter_mixed_unpaid_edge P K H hK hH hres d radius L M W U hRW hRU hmax
        N O.port (blocks O Q) (selected O Q) (ends O Q)
        (fun t => hmixed ▸ component_partition O Q t) hL hd0 hd hip hjp hx hy

end AssembledPathFamilies
end MinorFreeSpanners
