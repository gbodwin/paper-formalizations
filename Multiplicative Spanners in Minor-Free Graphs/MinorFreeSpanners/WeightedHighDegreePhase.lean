import MinorFreeSpanners.WeightedHighDegreeClusters
import MinorFreeSpanners.HighDegreeCredit
import MinorFreeSpanners.MarkedClusterEdges
import MinorFreeSpanners.ClusterGirth

/-! The actual high-degree phase with a conserved credit inequality. Pooled
payment is charged only for original host edges whose two old clusters are
marked; edges touching the low-degree residual remain for subsequent phases. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

theorem exists_weighted_high_degree_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D M L g : ℝ}
    (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G)
    (hD : 0≤D) (hM : 0≤M) (hL : 0<L)
    (hweight : ∀ e∈B.edgeSet, w e ≤ M)
    (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet, 0≤w e)
    (hlight : ∀ e∈A.edgeSet, w e < L) (hheavy : ∀ e∈B.edgeSet, L≤w e)
    (r h : ℕ) (hr : 1≤r) (hh : 0<h) (hfree : CliqueMinorFree G h)
    (hgeometry : ((2*r:ℕ):ℝ)*(1+D/L) ≤ g)
    (q : ℕ) (credit : I → ℝ) (b R : ℝ) (hb : 0≤b)
    (hc : ∀ i, b ≤ credit i)
    (hreserve : 2*R ≤ (q+1:ℕ)*b)
    (hpay : 2*(2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*M ≤ b) :
    ∃ centers : Finset I, ∃ groups : I → Finset I,
    ∃ F : ClusterFamily (I := {c // c∈centers}) G w (4*(D+M)+D),
      (∀ c∈centers, closedNeighborhood (C.graph B) c ⊆ groups c) ∧
      (∀ c∈centers, q+1 ≤ (groups c).card) ∧
      (∀ c : {c // c∈centers},
        F.branch c = {x | ∃ i∈groups c.val, x∈C.branch i}) ∧
      (∀ i, i∉centers.biUnion groups → (C.graph B).degree i < q) ∧
      (∀ c∈centers, R ≤ (∑ i∈groups c, credit i)/2) ∧
      (∑ e∈C.markedEdges B (centers.biUnion groups), w e) +
        (∑ c∈centers, (∑ i∈groups c, credit i)/2) ≤
        ∑ i∈centers.biUnion groups, credit i := by
  classical
  have hrR : (2:ℝ) ≤ (2*r:ℕ) := by exact_mod_cast (show 2≤2*r by omega)
  have hratio : 0≤D/L := div_nonneg hD hL.le
  have hbase : 2*(1+D/L) ≤ g :=
    (mul_le_mul_of_nonneg_right hrR (by linarith)).trans hgeometry
  have hg : 2≤g := by linarith
  have hbudget : 2*D ≤ (g-2)*L := by
    have hb := mul_le_mul_of_nonneg_right hbase hL.le
    have he : 2*(1+D/L)*L = 2*L+2*D := by field_simp [hL.ne']
    rw [he] at hb
    nlinarith only [hb]
  have hquotient := C.girth hA hB (2*r) hG hw hlight hheavy hL hD hgeometry
  obtain ⟨centers,groups,F,_,hcore,hsize,hdis,hbranch,hlow⟩ :=
    exists_weighted_high_degree_clusters C hA hB (add_nonneg hD hM) hweight q
  have hedges := marked_girth_minor_free_edge_bound (C.graph B) (centers.biUnion groups)
    r h hr hh (C.minorFree hA hB hfree) hquotient
  obtain ⟨hkeep,hpaid⟩ := high_degree_credit_accounting (C.graph B) centers groups
    hdis q hsize credit (2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ))) M b R hM hb
    (fun i _ => hc i) hreserve hpay hedges
  have hcount := C.marked_edges_card_le_of_girth hA hB (centers.biUnion groups)
    hG hw hlight hheavy hg hD hL hbudget
  have hcountR : ((C.markedEdges B (centers.biUnion groups)).card:ℝ) ≤
      (((C.graph B).induce (centers.biUnion groups : Set I)).edgeFinset.card:ℝ) := by
    exact_mod_cast hcount
  have hcost := (C.marked_edges_weight_le (centers.biUnion groups) M hweight).trans
    (mul_le_mul_of_nonneg_right hcountR hM)
  exact ⟨centers,groups,F,hcore,hsize,hbranch,hlow,hkeep,by linarith⟩

end MinorFreeSpanners
