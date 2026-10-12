import MinorFreeSpanners.WeightedJoinedArms
import MinorFreeSpanners.ShortCycleCore

/-! A heavy edge between far interior points of one original path supplies
either an actual short-cycle core or two disjoint four-arm carriers. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem same_path_core_dichotomy (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (B : SimpleGraph V)
    {u v x y : I} (l : H.Walk x u) (m : H.Walk x y) (r : H.Walk y v)
    (hp : (l.reverse.append (m.append r)).IsPath) (hL : 0<L)
    (hd0 : ∀ i∈(l.reverse.append (m.append r)).support,0≤d i+1)
    (hd : ∀ i∈(l.reverse.append (m.append r)).support,d i≤D)
    (hleft : L≤pathMass (fun i => d i+1) l)
    (hright : L≤pathMass (fun i => d i+1) r)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : B.Adj a b) :
    ∃ S : Finset I,S⊆(l.reverse.append (m.append r)).support.toFinset ∧
      (C.ShortCycleCore H d L B S ∨ C.FourArmCore H d L B S) := by
  classical
  by_cases hm : pathMass (fun i => d i+1) m≤2*(L+D+1)
  · obtain ⟨S,hS,hsub⟩ := C.short_cycle_core_of_paths H d L B l m r hp hL hd hleft hright hm ha hb hab
    exact ⟨S,hsub,Or.inl hS⟩
  have hms : ∀ i∈m.support,i∈(l.reverse.append (m.append r)).support := by
    intro i hi
    simp only [Walk.mem_support_append_iff]
    exact Or.inr (Or.inl hi)
  obtain ⟨s,t,ml,gap,mr,he,hgap,hml,_,hmr,_⟩ := exists_separated_path_pieces
    (fun i => d i+1) (D+1) L m hp.of_append_right.of_append_left hL
    (fun i hi => hd0 i (hms i hi)) (fun i hi => by have hh:=hd i (hms i hi);linarith)
    (by linarith)
  have hewhole : l.reverse.append (m.append r)=
      (l.reverse.append ml).append (gap.append (mr.append r)) := by
    rw [he]
    simp only [Walk.append_assoc]
  have hwhole := hewhole ▸ hp
  have hdis := separated_path_supports (l.reverse.append ml) gap (mr.append r) hwhole hgap
  have hls : (l.reverse.append ml).support.toFinset⊆(l.reverse.append (m.append r)).support.toFinset := by
    intro i hi
    apply List.mem_toFinset.mpr
    rw [hewhole,Walk.mem_support_append_iff]
    exact Or.inl (List.mem_toFinset.mp hi)
  have hrs : (mr.append r).support.toFinset⊆(l.reverse.append (m.append r)).support.toFinset := by
    intro i hi
    apply List.mem_toFinset.mpr
    rw [hewhole]
    exact (Walk.mem_support_append_iff _ _).mpr (Or.inr
      ((Walk.mem_support_append_iff _ _).mpr (Or.inr (List.mem_toFinset.mp hi))))
  obtain ⟨P,hP⟩ := exists_weighted_joined_arms (fun i => d i+1) L (D+1) l ml
    hwhole.of_append_left hL
    (fun i hi => by have hh:=hd i (List.mem_toFinset.mp (hls (List.mem_toFinset.mpr hi)));linarith) hleft hml
  obtain ⟨Q,hQ⟩ := exists_weighted_joined_arms (fun i => d i+1) L (D+1) mr.reverse r
    (by simpa only [Walk.reverse_reverse] using hwhole.of_append_right.of_append_right) hL
    (fun i hi => by
      have hi' : i∈(mr.append r).support := by simpa only [Walk.reverse_reverse] using hi
      have hh:=hd i (List.mem_toFinset.mp (hrs (List.mem_toFinset.mpr hi')))
      linarith)
    (by simpa only [pathMass_reverse] using hmr) hright
  simp only [Walk.reverse_reverse] at hQ
  refine ⟨P.carrier∪Q.carrier,Finset.union_subset (hP.trans hls) (hQ.trans hrs),Or.inr ?_⟩
  exact ⟨x,y,P,Q,Finset.disjoint_of_subset_left hP (Finset.disjoint_of_subset_right hQ hdis),rfl,a,ha,b,hb,hab⟩

end ClusterFamily
end MinorFreeSpanners
