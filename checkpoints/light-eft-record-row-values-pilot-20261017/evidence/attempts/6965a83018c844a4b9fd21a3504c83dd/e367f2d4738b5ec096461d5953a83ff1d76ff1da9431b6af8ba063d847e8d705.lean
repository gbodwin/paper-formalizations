import LightEFTSpanners.NativeCenterElimination

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
universe u v
variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
/-- After the finite split trace has exhausted the center's nonloop edge
identities, deleting that isolated center and its loops preserves every
terminal cut exactly. This is an actual native vertex-domain reduction. -/
theorem centerCore_cut_of_zero_inc (G : Graph (Option V) E)
    (hzero : Fintype.card (CenterInc G)=0) (S : Finset V) :
    cutSize G (liftSet S)=cutSize (centerCore G) (S:Set V) := by
  have : IsEmpty (CenterInc G) := Fintype.card_eq_zero_iff.mp hzero
  rw [cutSize_center_decomposition]
  simp [mass]

/-- The center-free native graph retains actual edge-fault connectivity
for every required pair. No graph-distance or flow surrogate is used. -/
theorem centerCore_required_of_zero_inc (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ) (hconn : RequiredConnectivity G P k)
    (hzero : Fintype.card (CenterInc G)=0) :
    ∀ a b,P a b → ∃ (ha : a∈(centerCore G).vertexSet) (hb : b∈(centerCore G).vertexSet),
      FaultConnected (centerCore G) (2*k) ⟨a,ha⟩ ⟨b,hb⟩ := by
  classical
  intro a b hp
  obtain ⟨ha,hb,_⟩ := hconn a b hp
  refine ⟨ha,hb,faultConnected_of_cut_lower _ ?_⟩
  intro S haS hbS
  have hsep : Separates P S.toFinset := ⟨a,b,hp,Or.inl ⟨by simpa,by simpa⟩⟩
  have h := requiredConnectivity_cut_lower G P k hconn S.toFinset
  rw [centerCore_cut_of_zero_inc G hzero,Set.coe_toFinset] at h
  simp only [requirement,hsep,ite_true] at h
  unfold cutSize at h
  exact_mod_cast h

/-- Eulerian parity survives deleting the exhausted center. -/
theorem centerCore_even_of_zero_inc (G : Graph (Option V) E)
    (hdeg : ∀ x,Even (nativeDegree G x)) (hzero : Fintype.card (CenterInc G)=0) :
    ∀ x,Even (nativeDegree (centerCore G) x) := by
  apply even_degrees_of_even_cuts
  intro S
  have h := even_cut_of_even_degrees G hdeg (liftSet S.toFinset)
  rw [centerCore_cut_of_zero_inc G hzero,Set.coe_toFinset] at h
  exact h

/-- Complete single-Steiner-vertex reduction. The output includes a finite
trace of the proved literal splits, the exact terminal vertex domain, even
actual degrees, and all required 2k-edge-fault connections. Expanding a packed
forest through this trace, and the multi-island packing induction, remain
separate obligations. -/
theorem exists_native_steiner_reduction (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ) (hdeg : ∀ x,Even (nativeDegree G x))
    (hconn : RequiredConnectivity G P k) :
    ∃ (F : Type v) (hF : Fintype F) (H : Graph (Option V) F),
      CenterEliminationResult G P k hF H ∧
      (centerCore H).vertexSet={x | some x∈G.vertexSet} ∧
      (letI := hF; ∀ x,Even (nativeDegree (centerCore H) x)) ∧
      (letI := hF; ∀ a b,P a b →
        ∃ (ha : a∈(centerCore H).vertexSet) (hb : b∈(centerCore H).vertexSet),
          FaultConnected (centerCore H) (2*k) ⟨a,ha⟩ ⟨b,hb⟩) := by
  obtain ⟨F,hF,H,hH⟩ := exists_native_center_elimination G P k hdeg hconn
  let := hF
  have hkeep := hH
  obtain ⟨_,hzero,hconnH,hdegH,hvert⟩ := hH
  refine ⟨F,hF,H,hkeep,?_,centerCore_even_of_zero_inc H hdegH hzero,
    centerCore_required_of_zero_inc H P k hconnH hzero⟩
  change {x | some x∈H.vertexSet}={x | some x∈G.vertexSet}
  rw [hvert]
end LightEFTSpanners.EvenSplitting
