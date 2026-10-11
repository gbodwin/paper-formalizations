import MinorFreeSpanners.BipartiteCleanContraction
import MinorFreeSpanners.RightStarEdgeBudget

/-! Actual right-side minors after quantitative star cleaning. The full
initial star family and the original left-degree regularity are explicit;
selection of that family and the paper's density increment remain separate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- The actual right quotient retains the regular-degree mass of the selected
leaves, less the independently proved full-contraction edge budget. -/
theorem IsStarPacking.right_quotient_regular_budget {G : SimpleGraph V}
    {A B C : Finset V} {ell m : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (hcover : A ∪ B=Finset.univ) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hreg : ∀ a ∈ A, G.degree a=m) (loss : ℝ)
    (hedge : (G.edgeFinset.card:ℝ) ≤
      (fullStarContraction G C L).edgeFinset.card+loss*C.card) :
    (m:ℝ)*ell*C.card ≤ (rightStarQuotient G B C L).edgeFinset.card+loss*C.card := by
  classical
  have hAB : Disjoint A B := Finset.disjoint_coe.mp hG.disjoint
  have hr := Nat.cast_le (α:=ℝ).mpr
    (h.right_quotient_edge_budget hAB hCB hcover m (fun a ha => (hreg a ha).le))
  have hsub : C.biUnion L ⊆ A := by
    intro a ha
    obtain ⟨b,_,ha⟩ := Finset.mem_biUnion.mp ha
    exact h.2.1 b ha
  have hl : (C.biUnion L).card=ell*C.card := calc
    _ = ∑ b ∈ C, (L b).card := h.size_eq_sum
    _ = ∑ _b ∈ C, ell := Finset.sum_congr rfl hfull
    _ = _ := by simp [Nat.mul_comm]
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [hl] at hc
  have he : G.edgeFinset.card=m*A.card := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hG]
    calc
      _ = ∑ _a ∈ A, m := Finset.sum_congr rfl hreg
      _ = _ := by simp [Nat.mul_comm]
  rw [he] at hedge
  have hcR : ((A \ C.biUnion L).card:ℝ)+(ell:ℝ)*C.card=A.card := by exact_mod_cast hc
  push_cast at hedge hr
  nlinarith [congrArg (fun x : ℝ => (m:ℝ)*x) hcR]

/-- A genuine bounded minor on exactly the original right-side vertex count,
with its retained edge mass, or a genuine small dense induced witness. -/
theorem exists_bipartite_dense_induced_or_right_minor
    (G : SimpleGraph V) (A B C : Finset V) (ell D m : ℕ)
    (k d : ℝ) (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k)
    (hd : k ≤ d) (hD : (D:ℝ) ≤ 5*k^2*d)
    (hUnmated : Unmated G (5*k^2) (1/(100*k)) (1/(100*k^2)) d)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (hCB : C ⊆ B) (hcover : A ∪ B=Finset.univ)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G (d/(100*k^2)) (insert b (L b:Set V)))
    (hsmall : ∀ x ∈ C ∪ C.biUnion L, G.degree x ≤ D)
    (hreg : ∀ a ∈ A, G.degree a=m) :
    (∃ H : Finset V, (H.card:ℝ) ≤ 10*k^3*d ∧
      (d/(100*k))^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ) ∧
      d/(400000*k^5)*(H.card:ℝ) ≤ ((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      C.biUnion M=C.biUnion L ∧
      Fintype.card {i : StarContractionVertex C M // i ∈ rightStarKeep B C M}=B.card ∧
      ∃ model : MinorModel (rightStarQuotient G B C M) G,
        model.IsBounded (ell+1) ∧
        (m:ℝ)*ell*C.card ≤ (rightStarQuotient G B C M).edgeFinset.card+
          (2*ell*d/k)*C.card) := by
  classical
  obtain hs | ⟨M,hM,hMf,_hfree,hcov,_model,_hw,_hm,_hc,_hn,he⟩ :=
    exists_bipartite_dense_induced_or_small_loss_contraction G A B C ell D k d
      hk hell hellk hd hD hUnmated L hG hCB hL hfull hfree hsmall
  · exact Or.inl hs
  · right
    have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
    refine ⟨M,hM,hMf,hcov,?_,hM.rightMinorModel hAC,
      hM.rightMinorModel_bounded hAC,?_⟩
    · simpa only [Fintype.card_coe] using hM.right_keep_card (Finset.disjoint_coe.mp hG.disjoint) hCB
    · exact hM.right_quotient_regular_budget hG hCB hcover hMf hreg (2*ell*d/k) he

end MinorFreeSpanners
