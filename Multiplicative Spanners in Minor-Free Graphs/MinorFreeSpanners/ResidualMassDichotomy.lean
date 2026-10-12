import MinorFreeSpanners.ResidualForestPaths
import MinorFreeSpanners.ResidualComponents

/-! Classify the actual residual components by the mass of their simple paths.
A small component need not have small total mass. Branching maximality makes
only the components containing a long path into degree-two spanning paths. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def LongResidualComponent {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (d : I → ℝ) (L : ℝ) (t : (H.induce (R:Set I)).ConnectedComponent) : Prop :=
  ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
    (∀ i∈p.support,i∈ResidualComponents.block H R t) ∧ L≤pathMass d p

 theorem short_residual_component {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (d : I → ℝ) (L : ℝ) (t : (H.induce (R:Set I)).ConnectedComponent)
    (ht : ¬LongResidualComponent H R d L t) {x y : I} (p : H.Walk x y)
    (hp : p.IsPath) (hs : ∀ i∈p.support,i∈ResidualComponents.block H R t) :
    pathMass d p<L := by
  apply lt_of_not_ge
  intro hm
  exact ht ⟨x,y,p,hp,hs,hm⟩

 theorem long_residual_component_degree {I : Type*} [Fintype I]
    (H : SimpleGraph I) (R : Finset I) (d : I → ℝ) (L : ℝ)
    (hmax : ∀ W : Finset I,ConnectedWithin H W → W⊆R →
      (∃ x y,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧ L≤pathMass d p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2)
    (t : (H.induce (R:Set I)).ConnectedComponent) (ht : LongResidualComponent H R d L t) :
    ∀ i∈ResidualComponents.block H R t,((H.neighborFinset i)∩R).card≤2 := by
  classical
  intro i hi
  have he : (H.neighborFinset i)∩R=(H.neighborFinset i)∩ResidualComponents.block H R t := by
    ext j
    constructor
    · intro hj
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hj).1,
        ResidualComponents.closed_adj H R t hi (Finset.mem_inter.mp hj).2
          ((H.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hj).1)⟩
    · intro hj
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hj).1,
        ResidualComponents.subset H R t (Finset.mem_inter.mp hj).2⟩
  rw [he]
  exact hmax _ (ResidualComponents.connected H R t) (ResidualComponents.subset H R t) ht i hi

 theorem long_residual_component_spanning_path {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : H.IsAcyclic) (R : Finset I) (d : I → ℝ) (L : ℝ)
    (hd : ∀ i∈R,0≤d i)
    (hmax : ∀ W : Finset I,ConnectedWithin H W → W⊆R →
      (∃ x y,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧ L≤pathMass d p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2)
    (t : (H.induce (R:Set I)).ConnectedComponent) (ht : LongResidualComponent H R d L t) :
    ∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=ResidualComponents.block H R t ∧
      L≤pathMass d p := by
  classical
  obtain ⟨x,_,y,_,p,hp,hps⟩ := connected_forest_degree_two_path H hH
    (ResidualComponents.block H R t) (ResidualComponents.connected H R t)
    (ResidualComponents.nonempty H R t)
    (hmax _ (ResidualComponents.connected H R t) (ResidualComponents.subset H R t) ht)
  obtain ⟨a,b,q,hq,hqs,hm⟩ := ht
  refine ⟨x,y,p,hp,hps,hm.trans ?_⟩
  unfold pathMass
  rw [hps]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => hqs i (List.mem_toFinset.mp hi))
    (fun i hi _ => hd i (ResidualComponents.subset H R t hi))

end MinorFreeSpanners
