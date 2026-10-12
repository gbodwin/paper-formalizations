import MinorFreeSpanners.PathCoreResidual
import MinorFreeSpanners.InteriorPathBlock

/-! Actual path decomposition orients two original vertices without assuming
an order on the block family. Residual core maximality forbids a heavy edge
between weighted interior vertices, including vertices on the same path. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem no_residual_ordered_interior_edge (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (hforest : H.IsAcyclic) (d : I → ℝ) (L : ℝ) (R U : Finset I)
    (hmax : ∀ S : Finset I,S⊆R → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    {u v x y : I} (p : H.Walk u v) (hp : p.IsPath)
    (hx : WeightedInterior (fun i => d i+1) L p x)
    (hy : WeightedInterior (fun i => d i+1) L p y)
    (horder : x∈(p.takeUntil y hy.choose).support)
    (hR : p.support.toFinset⊆R) (hU : Disjoint p.support.toFinset U)
    (hL : 0<L) (hd0 : ∀ i∈R,0≤d i+1) (hd : ∀ i∈R,d i≤D)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) : ¬B.Adj a b := by
  classical
  intro hab
  let q := p.takeUntil y hy.choose
  let l := p.takeUntil x hx.choose
  let m := q.dropUntil x horder
  let r := p.dropUntil y hy.choose
  have he : q.takeUntil x horder=l := congrArg Subtype.val
    ((hforest.subsingleton_path u x).elim
      ⟨q.takeUntil x horder,(hp.takeUntil hy.choose).takeUntil horder⟩
      ⟨l,hp.takeUntil hx.choose⟩)
  have hpEq : l.reverse.reverse.append (m.append r)=p := by
    rw [Walk.reverse_reverse,Walk.append_assoc,←he]
    exact (congrArg (fun z => z.append r) (q.take_spec horder)).trans (p.take_spec hy.choose)
  have hout := C.residual_same_path_edge_near_end H d L R U hmax l.reverse m r
    (hpEq.symm ▸ hp) hL (hpEq.symm ▸ hR) (hpEq.symm ▸ hU) hd0 hd ha hb hab
  rcases hout with h | h
  · have hh := hx.choose_spec.1
    simp only [pathMass_reverse] at h
    exact (not_lt_of_ge hh) h
  · exact (not_lt_of_ge hy.choose_spec.2) h

 theorem no_residual_same_path_interior_edge (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (hforest : H.IsAcyclic) (d : I → ℝ) (L : ℝ) (R U : Finset I)
    (hmax : ∀ S : Finset I,S⊆R → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    {u v x y : I} (p : H.Walk u v) (hp : p.IsPath)
    (hx : WeightedInterior (fun i => d i+1) L p x)
    (hy : WeightedInterior (fun i => d i+1) L p y)
    (hR : p.support.toFinset⊆R) (hU : Disjoint p.support.toFinset U)
    (hL : 0<L) (hd0 : ∀ i∈R,0≤d i+1) (hd : ∀ i∈R,d i≤D)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) : ¬B.Adj a b := by
  classical
  by_cases ho : x∈(p.takeUntil y hy.choose).support
  · exact C.no_residual_ordered_interior_edge H hforest d L R U hmax p hp hx hy ho
      hR hU hL hd0 hd ha hb
  have ho' : y∈(p.takeUntil x hx.choose).support := by
    rw [Walk.takeUntil_eq_take,Walk.support_copy,Walk.support_take,
      List.mem_take_iff_idxOf_lt hx.choose] at ho
    rw [Walk.takeUntil_eq_take,Walk.support_copy,Walk.support_take,
      List.mem_take_iff_idxOf_lt hy.choose]
    omega
  intro hab
  exact C.no_residual_ordered_interior_edge H hforest d L R U hmax p hp hy hx ho'
    hR hU hL hd0 hd hb ha hab.symm

end ClusterFamily
end MinorFreeSpanners
