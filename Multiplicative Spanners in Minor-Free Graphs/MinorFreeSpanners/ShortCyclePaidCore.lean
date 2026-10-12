import MinorFreeSpanners.ShortCycleArms

/-! The short-cycle reserve surplus is proved from the actual heavy-edge
detour and weighted girth, then pays all low-degree charges. It is not an
input credit inequality. The three selected paths are original coarse walks. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem short_cycle_paid_core (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (d credit : I → ℝ) (L c b a M g ell : ℝ) (N : ℕ) {x y : I}
    (S : ShortCycleArms H d L D x y) (hD : 0≤D) (hc : 0≤c) (ha0 : 0≤a)
    (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ p : A.Walk a b,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hlight : ∀ e∈A.edgeSet,w e<ell) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hell : 1<ell) (hg : 2≤g)
    {u v : V} (hu : u∈C.branch x) (hv : v∈C.branch y) (huv : G.Adj u v)
    (hheavy : ell≤w s(u,v)) (hupper : w s(u,v)≤M)
    (hcredit : ∀ i∈S.carrier,c*d i≤credit i) (hbase : ∀ i∈S.carrier,c*b≤credit i)
    (hsmall : a*N+c*b/2≤c*((g-2)*ell-6*D-4))
    (hlarge : 2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b)) (hpay : 2*a≤c*b) :
    (∀ z,(∃ i∈S.carrier,z∈C.branch i) → ∀ t,(∃ i∈S.carrier,t∈C.branch i) →
      ∃ p : G.Walk z t,(∀ r∈p.support,∃ i∈S.carrier,r∈C.branch i) ∧
        walkWeight w p≤2*(L+2*D+1)+w s(u,v)) ∧
    c*(2*(L+2*D+1)+w s(u,v))+a*S.carrier.card+c*b/2≤
      (∑ i∈S.carrier,credit i)+c*(internalEdges H S.carrier).card := by
  classical
  have hbridge : ∀ i j,H.Adj i j → ∃ a∈C.branch i,∃ b∈C.branch j,
      ∃ _hab : G.Adj a b,w s(a,b)≤1 := by
    intro i j hij
    obtain ⟨_,a,hai,b,hbj,hab⟩ := hH hij
    exact ⟨a,hai,b,hbj,hT hab,(hunit _ hab).le⟩
  constructor
  · have hp := C.short_cycle_walks hA H d L S.left S.middle S.right
      S.left_path S.middle_path S.right_path hD hd1 hdD S.left_upper.le S.right_upper.le
      S.middle_upper hdiam hbridge hu hv huv (hw _ huv)
    simpa only [S.carrier_eq] using hp
  · have hgap := C.coarse_path_detour_gap hA hT H hH d hdiam g ell hG hw hlight hunit
      hell S.middle S.middle_path hu hv huv hheavy
    have hraw := S.credit_gap credit c (w s(u,v)) g ell hc hg (hdD x) (hdD y) hheavy hgap.le hcredit
    apply bounded_surplus_payment S.carrier credit c (2*(L+2*D+1)+w s(u,v))
      (internalEdges H S.carrier).card ((g-2)*ell-6*D-4) b a N hc ha0
      (Nat.cast_nonneg _) hbase hraw hsmall _ hpay
    have hmul := mul_le_mul_of_nonneg_left hupper (show 0≤2*c by linarith)
    nlinarith

end ClusterFamily
end MinorFreeSpanners
