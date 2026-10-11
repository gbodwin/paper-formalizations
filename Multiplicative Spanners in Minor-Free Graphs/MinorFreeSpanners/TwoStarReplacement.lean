import MinorFreeSpanners.StarExtensionExactLoss
import MinorFreeSpanners.StarSubfamilyMembership

/-! Uncontract one actual old star and replace it by two protected stars.
The two growth losses fit inside the extra clean allowance, so the resulting
actual family has strictly more centers while retaining every other old star. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem residual_not_center (C : Finset V) (L : V → Finset V) {x : V}
    (hx : x ∈ starResidual C L) : x ∉ C := by
  intro hc
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨x,hc,Finset.mem_insert_self x (L x)⟩)

/-- A precise replacement theorem. The input neighbor sets are original-host
residual vertices; only their proved size/adjacency/degree properties are used. -/
theorem replace_one_star_by_two (G : SimpleGraph V)
    (k : ℕ) (C T1 T2 : Finset V) (L : V → Finset V) (b u v : V)
    (K eps1 eps2 d : ℝ)
    (h : SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L)
    (hb : b ∈ C) (hu : u ∈ insert b (L b)) (hv : v ∈ insert b (L b)) (huv : u ≠ v)
    (hT1R : T1 ⊆ starResidual C L) (hT2R : T2 ⊆ starResidual C L)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hT1 : 2*eps1*d ≤ (T1.card:ℝ)) (hT2 : 3*eps1*d ≤ (T2.card:ℝ))
    (hadj1 : ∀ x ∈ T1, G.Adj u x) (hadj2 : ∀ x ∈ T2, G.Adj v x)
    (hsmall1 : ∀ x ∈ T1, (G.degree x:ℝ) ≤ K*d)
    (hsmall2 : ∀ x ∈ T2, (G.degree x:ℝ) ≤ K*d)
    (hDense : ¬∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) :
    ∃ L' : V → Finset V,
      SmallCleanStarForest G k (K*d) (4*(eps2*d)) (insert v (insert u (C.erase b))) L' ∧
      (∀ a ∈ C.erase b, L' a=L a) ∧
      (insert v (insert u (C.erase b))).card=C.card+1 := by
  classical
  let C0 := C.erase b
  have hsub : C0 ⊆ C := Finset.erase_subset b C
  have h0 := h.1.restrict hsub
  have hsmall0 : ∀ x ∈ C0.biUnion (fun a => insert a (L a)), (G.degree x:ℝ) ≤ K*d :=
    fun x hx => h.2.1 x (covered_mono_centers C C0 L hsub hx)
  have huR0 : u ∈ starResidual C0 L := h.1.erased_branch_residual hb hu
  have hvR0 : v ∈ starResidual C0 L := h.1.erased_branch_residual hb hv
  have huC0 := residual_not_center C0 L huR0
  have hT1R0 : T1 ⊆ starResidual C0 L :=
    fun x hx => residual_mono_centers C C0 L hsub (hT1R hx)
  have hsmallU : ∀ x ∈ (insert u T1:Set V), (G.degree x:ℝ) ≤ K*d := by
    intro x hx
    rcases hx with he | hx
    · have he' : x=u := he
      subst x
      exact h.2.1 u (Finset.mem_biUnion.mpr ⟨b,hb,hu⟩)
    · exact hsmall1 x hx
  obtain ⟨L1,h1,hold1,hS1,hs1,he01⟩ :=
    (extend_forest_with_loss_or_dense G k C0 T1 L u K eps1 eps2 d
      h0 hsmall0 huR0 hT1R0 hk hK hd he1 he1' he2 hq hkd hT1 hadj1 hsmallU).resolve_left hDense
  let S1 := insert u (L1 u)
  let C1 := insert u C0
  have hsize1 : S1.card=k := h1.2.1 u (Finset.mem_insert_self u C0)
  have hcover1 := covered_insert_of_old_leaves C0 L L1 u hold1
  have hvNotR : v ∉ starResidual C L := by
    intro hh
    exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_biUnion.mpr ⟨b,hb,hv⟩)
  have hvNotS1 : v ∉ S1 := by
    intro hh
    rcases Finset.mem_insert.mp (hS1 hh) with he | hh
    · exact huv he.symm
    · exact hvNotR (hT1R hh)
  have hvR1 : v ∈ starResidual C1 L1 := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ v,?_⟩
    rw [hcover1]
    exact fun hh => (Finset.mem_union.mp hh).elim hvNotS1 (Finset.mem_sdiff.mp hvR0).2
  have hvC1 := residual_not_center C1 L1 hvR1
  let T2' := T2 \ S1
  have hT2R1 : T2' ⊆ starResidual C1 L1 := by
    intro x hx
    have hxT := (Finset.mem_sdiff.mp hx).1
    have hxS := (Finset.mem_sdiff.mp hx).2
    have hxR0 := residual_mono_centers C C0 L hsub (hT2R hxT)
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ x,?_⟩
    rw [hcover1]
    exact fun hh => (Finset.mem_union.mp hh).elim hxS (Finset.mem_sdiff.mp hxR0).2
  have hc2 : (T2.card:ℝ) ≤ (T2'.card:ℝ)+k := by
    have hh : T2.card ≤ T2'.card+S1.card := Finset.card_le_card_sdiff_add_card
    rw [hsize1] at hh
    exact_mod_cast hh
  have hT2' : 2*eps1*d ≤ (T2'.card:ℝ) := by linarith
  have hadj2' : ∀ x ∈ T2', G.Adj v x := fun x hx => hadj2 x (Finset.mem_sdiff.mp hx).1
  have hsmallV : ∀ x ∈ (insert v T2':Set V), (G.degree x:ℝ) ≤ K*d := by
    intro x hx
    rcases hx with he | hx
    · have he' : x=v := he
      subst x
      exact h.2.1 v (Finset.mem_biUnion.mpr ⟨b,hb,hv⟩)
    · exact hsmall2 x (Finset.mem_sdiff.mp hx).1
  obtain ⟨L2,h2,hold2,_,hs2,he12⟩ :=
    (extend_forest_with_loss_or_dense G k C1 T2' L1 v K eps1 eps2 d
      h1 hs1 hvR1 hT2R1 hk hK hd he1 he1' he2 hq hkd hT2' hadj2' hsmallV).resolve_left hDense
  have hcard : (insert v (insert u (C.erase b))).card=C.card+1 := by
    rw [Finset.card_insert_of_notMem hvC1,Finset.card_insert_of_notMem huC0,
      Finset.card_erase_of_mem hb]
    have hpos : 0<C.card := Finset.card_pos.mpr ⟨b,hb⟩
    omega
  refine ⟨L2,⟨h2,hs2,?_⟩,?_,hcard⟩
  · have heOld := h.2.2
    have heSplit : ((fullStarContraction G C L).edgeFinset.card:ℝ) ≤
        (fullStarContraction G C0 L).edgeFinset.card := by
      exact_mod_cast h.1.subfamily_edges hsub
    have hkm : ((k-1:ℕ):ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hp := mul_le_mul_of_nonneg_right hkm (show 0 ≤ eps2*d by linarith)
    change (G.edgeFinset.card:ℝ) ≤
      (fullStarContraction G (insert v (insert u (C.erase b))) L2).edgeFinset.card +
        (4*(eps2*d))*(k*(insert v (insert u (C.erase b))).card:ℕ)
    rw [hcard]
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] at heOld ⊢
    dsimp [C0,C1] at he01 he12 heSplit
    nlinarith
  · intro a ha
    exact (hold2 a (Finset.mem_insert_of_mem ha)).trans (hold1 a ha)

end MinorFreeSpanners
