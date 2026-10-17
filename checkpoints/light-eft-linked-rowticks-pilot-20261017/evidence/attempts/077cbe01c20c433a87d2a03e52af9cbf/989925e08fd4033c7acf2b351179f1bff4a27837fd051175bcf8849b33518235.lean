import LightEFTSpanners.NativeCenterSplit
import LightEFTSpanners.NativeEvenAdmissibility

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- All cuts of the native graph have even cardinality. This is stated on
actual edge identities and includes parallel edges; loops do not cross cuts. -/
def EvenCuts (G : Graph (Option V) E) : Prop := ∀ S : Set (Option V),Even (cutSize G S)

/-- Genuine pairwise edge-fault resilience, including actual vertex membership.
The center is never a required terminal. -/
def RequiredConnectivity (G : Graph (Option V) E) (P : V → V → Prop) (k : ℕ) : Prop :=
  ∀ a b,P a b → ∃ (ha : some a∈G.vertexSet) (hb : some b∈G.vertexSet),
    FaultConnected G (2*k) ⟨some a,ha⟩ ⟨some b,hb⟩

omit [Fintype V] [DecidableEq V] in
theorem requiredConnectivity_cut_lower (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ) (h : RequiredConnectivity G P k) (S : Finset V) :
    requirement P k S≤cutSize G (liftSet S) := by
  classical
  by_cases hs : Separates P S
  · obtain ⟨a,b,hp,hab⟩ := hs
    obtain ⟨ha,hb,hr⟩ := h a b hp
    have hs' : Separates P S := ⟨a,b,hp,hab⟩
    simp only [requirement,hs',ite_true]
    rcases hab with ⟨haS,hbS⟩ | ⟨hbS,haS⟩
    · have hc := faultConnected_le_cut G hr (liftSet S)
        ((some_mem_liftSet S a).mpr haS) (fun h => hbS ((some_mem_liftSet S b).mp h))
      unfold cutSize
      exact_mod_cast hc
    · have hc := faultConnected_le_cut G hr (liftSet S)ᶜ
        (fun h => haS ((some_mem_liftSet S a).mp h))
        (by simpa only [Set.mem_compl_iff,not_not] using (some_mem_liftSet S b).mpr hbS)
      have hc' : (2*k:ℤ)≤cutSize G (liftSet S)ᶜ := by
        unfold cutSize
        exact_mod_cast hc
      simpa only [cutSize_compl] using hc'
  · simp only [requirement,hs,ite_false]
    exact cutSize_nonneg _ _

omit [DecidableEq V] in
/-- Every set avoiding the center is literally a lifted finite terminal set. -/
theorem exists_liftSet (S : Set (Option V)) (hn : none∉S) :
    ∃ T : Finset V,liftSet T=S := by
  classical
  refine ⟨univ.filter (fun v => some v∈S),?_⟩
  ext x
  cases x with
  | none => simp [hn]
  | some v => simp

omit [DecidableEq V] in
/-- Center-free even cuts suffice, by complement symmetry, for every cut. -/
theorem evenCuts_of_lift (G : Graph (Option V) E)
    (h : ∀ S : Finset V,Even (cutSize G (liftSet S))) : EvenCuts G := by
  intro S
  by_cases hn : none∈S
  · obtain ⟨T,hT⟩ := exists_liftSet Sᶜ (by simpa)
    have ht := h T
    simpa only [hT,cutSize_compl] using ht
  · obtain ⟨T,rfl⟩ := exists_liftSet S hn
    exact h T

omit [DecidableEq V] in
/-- All required native fault connections follow from the actual center-free
cut bounds, provided their endpoints are actual vertices. -/
theorem requiredConnectivity_of_cuts (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ)
    (hmem : ∀ a b,P a b → some a∈G.vertexSet ∧ some b∈G.vertexSet)
    (hcuts : ∀ S : Finset V,requirement P k S≤cutSize G (liftSet S)) :
    RequiredConnectivity G P k := by
  intro a b hp
  obtain ⟨ha,hb⟩ := hmem a b hp
  refine ⟨ha,hb,faultConnected_of_cut_lower G ?_⟩
  intro S haS hbS
  have hbound (T : Finset V) (hsep : Separates P T) : (2*k:ℤ)≤cutSize G (liftSet T) := by
    have h := hcuts T
    simpa only [requirement,hsep,ite_true] using h
  by_cases hn : none∈S
  · obtain ⟨T,hT⟩ := exists_liftSet Sᶜ (by simpa)
    have haT : a∉T := by simpa only [←some_mem_liftSet,hT,Set.mem_compl_iff,not_not] using haS
    have hbT : b∈T := by simpa only [←some_mem_liftSet,hT,Set.mem_compl_iff] using hbS
    have h := hbound T ⟨a,b,hp,Or.inr ⟨hbT,haT⟩⟩
    rw [hT,cutSize_compl] at h
    unfold cutSize at h
    exact_mod_cast h
  · obtain ⟨T,hT⟩ := exists_liftSet S hn
    have haT : a∈T := by simpa only [←some_mem_liftSet,hT] using haS
    have hbT : b∉T := by simpa only [←some_mem_liftSet,hT] using hbS
    have h := hbound T ⟨a,b,hp,Or.inl ⟨haT,hbT⟩⟩
    rw [hT] at h
    unfold cutSize at h
    exact_mod_cast h

/-- Eulerian required-pair splitting, proved from native cuts. For any chosen
nonloop center-edge identity, the constructed distinct partner preserves every
required 2k-fault connection. All cut parities are preserved as well. This is
the uniform-threshold Eulerian case needed by the Steiner forest argument. -/
theorem exists_eulerian_required_split (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ) (hconn : RequiredConnectivity G P k)
    (heven : EvenCuts G) (hdegree : 2≤Fintype.card (CenterInc G)) (i : CenterInc G) :
    ∃ j : CenterInc G,j≠i ∧ RequiredConnectivity (centerSplit G i j) P k ∧
      EvenCuts (centerSplit G i j) := by
  obtain ⟨j,hji,hj⟩ := native_exists_admissible_partner G P k
    (requiredConnectivity_cut_lower G P k hconn) (fun S => heven (liftSet S)) hdegree i
  have hcuts (S : Finset V) : requirement P k S≤cutSize (centerSplit G i j) (liftSet S) := by
    have hc := centerSplit_cutSize G i j (Ne.symm hji) S
    by_cases hS : centerEnd G i∈S ∧ centerEnd G j∈S
    · have h := hj S hS.1 hS.2
      simp only [hS] at hc
      omega
    · have h := requiredConnectivity_cut_lower G P k hconn S
      simp only [hS,ite_false,add_zero] at hc
      omega
  refine ⟨j,hji,requiredConnectivity_of_cuts _ P k ?_ hcuts,evenCuts_of_lift _ ?_⟩
  · intro a b hp
    obtain ⟨ha,hb,_⟩ := hconn a b hp
    exact ⟨ha,hb⟩
  · intro S
    have hc := centerSplit_cutSize G i j (Ne.symm hji) S
    have h := heven (liftSet S)
    rw [hc] at h
    by_cases hS : centerEnd G i∈S ∧ centerEnd G j∈S
    · simp only [hS] at h
      exact even_add_two.mp h
    · simpa only [hS,ite_false,add_zero] using h
end LightEFTSpanners.EvenSplitting
