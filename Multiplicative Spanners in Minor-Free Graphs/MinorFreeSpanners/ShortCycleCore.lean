import MinorFreeSpanners.ShortCycleSelection

/-! A short-cycle carrier is witnessed by three consecutive actual subpaths
and an original heavy edge. No numerical payment is part of eligibility. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

def ShortCycleCore (C : ClusterFamily (I := I) A w D) (H : SimpleGraph I)
    (d : I → ℝ) (L : ℝ) (B : SimpleGraph V) (S : Finset I) : Prop :=
  ∃ x y,∃ Q : ShortCycleArms H d L D x y,S=Q.carrier ∧
    ∃ u∈C.branch x,∃ v∈C.branch y,B.Adj u v

 theorem ShortCycleCore.nonempty (C : ClusterFamily (I := I) A w D)
    {H : SimpleGraph I} {d : I → ℝ} {L : ℝ} {S : Finset I}
    (h : C.ShortCycleCore H d L B S) : S.Nonempty := by
  obtain ⟨x,y,Q,rfl,_⟩ := h
  exact Q.nonempty

 theorem short_cycle_core_of_paths (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (B : SimpleGraph V)
    {u v x y : I} (l : H.Walk x u) (m : H.Walk x y) (r : H.Walk y v)
    (hp : (l.reverse.append (m.append r)).IsPath) (hL : 0<L)
    (hd : ∀ i∈(l.reverse.append (m.append r)).support,d i≤D)
    (hleft : L≤pathMass (fun i => d i+1) l)
    (hright : L≤pathMass (fun i => d i+1) r)
    (hmiddle : pathMass (fun i => d i+1) m≤2*(L+D+1))
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : B.Adj a b) :
    ∃ S : Finset I,C.ShortCycleCore H d L B S ∧
      S⊆(l.reverse.append (m.append r)).support.toFinset := by
  obtain ⟨Q,_,hQ⟩ := exists_short_cycle_arms d L D l m r hp hL hd hleft hright hmiddle
  exact ⟨Q.carrier,⟨x,y,Q,rfl,a,ha,b,hb,hab⟩,hQ⟩

 theorem ShortCycleCore.paid [Fintype I] (C : ClusterFamily (I := I) A w D)
    {T G : SimpleGraph V} (hA : A≤G) (hB : B≤G) (hT : T≤G)
    (H : SimpleGraph I) (hH : H≤C.graph T) (d credit : I → ℝ)
    (L c b a M g ell : ℝ) (N : ℕ) {S : Finset I}
    (h : C.ShortCycleCore H d L B S) (hD : 0≤D) (hc : 0≤c) (ha0 : 0≤a)
    (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hlight : ∀ e∈A.edgeSet,w e<ell) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hell : 1<ell) (hg : 2≤g)
    (hheavy : ∀ e∈B.edgeSet,ell≤w e) (hupper : ∀ e∈B.edgeSet,w e≤M)
    (hcredit : ∀ i∈S,c*d i≤credit i) (hbase : ∀ i∈S,c*b≤credit i)
    (hsmall : a*N+c*b/2≤c*((g-2)*ell-6*D-4))
    (hlarge : 2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b)) (hpay : 2*a≤c*b) :
    ∃ radius : ℝ,2*(L+2*D+1)+ell≤radius ∧ radius≤2*(L+2*D+1)+M ∧
    (∀ z,(∃ i∈S,z∈C.branch i) → ∀ t,(∃ i∈S,t∈C.branch i) →
      ∃ p : G.Walk z t,(∀ r∈p.support,∃ i∈S,r∈C.branch i) ∧ walkWeight w p≤radius) ∧
    c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+c*(internalEdges H S).card := by
  obtain ⟨x,y,Q,rfl,u,hu,v,hv,huv⟩ := h
  have hp := C.short_cycle_paid_core hA hT H hH d credit L c b a M g ell N Q hD hc ha0
    hd1 hdD hdiam hG hw hlight hunit hell hg hu hv (hB huv) (hheavy _ huv)
    (hupper _ huv) hcredit hbase hsmall hlarge hpay
  exact ⟨2*(L+2*D+1)+w s(u,v),by linarith [hheavy s(u,v) huv],
    by linarith [hupper s(u,v) huv],hp⟩

end ClusterFamily
end MinorFreeSpanners
