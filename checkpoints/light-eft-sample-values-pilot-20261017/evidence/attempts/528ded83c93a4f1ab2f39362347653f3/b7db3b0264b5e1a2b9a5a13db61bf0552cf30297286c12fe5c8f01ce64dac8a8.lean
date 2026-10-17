import LightEFTSpanners.NativeMultigraphCore
import LightEFTSpanners.ContractedCoreCuts

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The minimal deficient-core argument gives a real lower bound on every
separating cut after complement contraction. Edge identities are retained;
this is the cut obligation in CS09 Lemma 2.4, not an assumed packing theorem. -/
theorem native_minimal_core_contracted_cut_lower (G : Graph V E)
    (K : Finset V) {k : ℕ}
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty →
      k≤(G.edgeCut (A:Set V)).toFinset.card)
    (a b : (K:Set V)) (S : Set (Option (K:Set V)))
    (ha : some a∈S) (hb : some b∉S) :
    k≤((G.map (collapseOutside (K:Set V))).edgeCut S).toFinset.card := by
  classical
  have hside (T : Set (Option (K:Set V))) (hn : none∉T)
      (x y : (K:Set V)) (hx : some x∈T) (hy : some y∉T) :
      k≤((G.map (collapseOutside (K:Set V))).edgeCut T).toFinset.card := by
    let A : Set V := collapseOutside (K:Set V) ⁻¹' T
    have hAK : A⊆(K:Set V) := collapse_preimage_subset _ _ hn
    have hxA : x.val∈A := (collapse_mem _ _ _).mpr hx
    have hyA : y.val∉A := fun h => hy ((collapse_mem _ _ _).mp h)
    have hsub : A.toFinset⊆K := by simpa using hAK
    have hne : A.toFinset≠K := by
      intro heq
      have hyK : y.val∈A.toFinset :=
        (congrArg (fun t : Finset V => y.val∈t) heq).mpr y.property
      exact hyA (by simpa using hyK)
    have hlower := hmin A.toFinset (lt_of_le_of_ne hsub hne)
      ⟨x.val,by simpa using hxA⟩
    rw [edgeCut_map]
    simpa [A] using hlower
  by_cases hn : none∈S
  · have h := hside Sᶜ (by simpa using hn) b a hb (by simpa using ha)
    simpa only [edgeCut_compl] using h
  · exact hside S hn a b ha hb

/-- Actual retained vertices have explicit original preimages in a native
multigraph contraction. The premise excludes ambient nonvertices from K. -/
noncomputable def nativeCoreVertex (G : Graph V E) (K : Finset V)
    (hactual : (K:Set V)⊆G.vertexSet) (a : (K:Set V)) :
    (G.map (collapseOutside (K:Set V))).vertexSet :=
  ⟨some a,⟨a.val,hactual a.property,by simp [collapseOutside,a.property]⟩⟩

/-- Minimal-core cut bounds yield genuine native post-fault walks in the
contracted multigraph, without a simplification that could merge parallel IDs. -/
theorem native_minimal_core_faultConnected (G : Graph V E) (K : Finset V) {k : ℕ}
    (hactual : (K:Set V)⊆G.vertexSet)
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty → k≤(G.edgeCut (A:Set V)).toFinset.card)
    (a b : (K:Set V)) :
    FaultConnected (G.map (collapseOutside (K:Set V))) k
      (nativeCoreVertex G K hactual a) (nativeCoreVertex G K hactual b) := by
  apply faultConnected_of_cut_lower
  intro S ha hb
  exact native_minimal_core_contracted_cut_lower G K hmin a b S ha hb

/-- Select and contract the real minimal core in a genuine finite multigraph
basic instance. All retained vertices are proved actual; no minimal-core or
contracted-connectivity conclusion is supplied as a hypothesis. -/
theorem native_exists_basic_faultConnected_core (G : Graph V E)
    {u v : G.vertexSet} {k : ℕ} (hsep : ¬FaultConnected G k u v)
    (hbasic : ∀ a : G.vertexSet,∃ b : G.vertexSet,a≠b ∧ FaultConnected G k a b) :
    ∃ K : Finset V,∃ hactual : (K:Set V)⊆G.vertexSet,
      K⊂G.vertexSet.toFinset ∧ 2≤K.card ∧ (G.edgeCut (K:Set V)).toFinset.card<k ∧
      (∀ a b : G.vertexSet,a.val∈K → FaultConnected G k a b → b.val∈K) ∧
      ∀ a b : (K:Set V),FaultConnected (G.map (collapseOutside (K:Set V))) k
        (nativeCoreVertex G K hactual a) (nativeCoreVertex G K hactual b) := by
  obtain ⟨K,hproper,htwo,hsmall,hclosed,hmin⟩ := native_exists_basic_small_core G hsep hbasic
  have hactual : (K:Set V)⊆G.vertexSet := by
    intro x hx
    exact Set.mem_toFinset.mp (hproper.subset hx)
  exact ⟨K,hactual,hproper,htwo,hsmall,hclosed,
    fun a b => native_minimal_core_faultConnected G K hactual hmin a b⟩
end LightEFTSpanners.MultigraphCuts
