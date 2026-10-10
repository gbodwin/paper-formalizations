import LightEFTSpanners.MultigraphFaultConnectivity

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [Fintype E] in
/-- Removing ambient nonvertices from a cut side does not change a native
multigraph cut. This prevents phantom vertices entering the minimal core. -/
theorem edgeCut_inter_vertexSet (G : Graph V E) (S : Set V) :
    G.edgeCut (S∩G.vertexSet)=G.edgeCut S := by
  ext e
  constructor
  · rintro ⟨u,v,h,⟨hu,_⟩,hv⟩
    exact ⟨u,v,h,hu,fun hvS => hv ⟨hvS,h.right_mem⟩⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨u,v,h,⟨hu,h.left_mem⟩,fun hvS => hv hvS.1⟩

omit [Fintype V] in
/-- A genuine small multigraph cut contains each entire fault-connectivity
class that it meets. Parallel edge identities contribute individually. -/
theorem native_small_cut_closed (G : Graph V E) {S : Set V} {k : ℕ}
    (hsmall : (G.edgeCut S).toFinset.card<k) {a b : G.vertexSet}
    (ha : a.val∈S) (hconn : FaultConnected G k a b) : b.val∈S := by
  by_contra hb
  exact (not_lt_of_ge (faultConnected_le_cut G hconn S ha hb)) hsmall

omit [Fintype V] in
/-- Finite inclusion-minimal strictly deficient sets in the native multigraph
model, using the actual cardinality of edge-identified cuts. -/
theorem native_exists_minimal_small_cut (G : Graph V E) {S : Finset V} {k : ℕ}
    (hS : S.Nonempty) (hsmall : (G.edgeCut (S:Set V)).toFinset.card<k) :
    ∃ K : Finset V,K⊆S ∧ K.Nonempty ∧ (G.edgeCut (K:Set V)).toFinset.card<k ∧
      ∀ A : Finset V,A⊂K → A.Nonempty → k≤(G.edgeCut (A:Set V)).toFinset.card := by
  classical
  have hex : ∃ n : ℕ,∃ K : Finset V,
      K⊆S ∧ K.Nonempty ∧ (G.edgeCut (K:Set V)).toFinset.card<k ∧ K.card=n :=
    ⟨S.card,S,Subset.rfl,hS,hsmall,rfl⟩
  obtain ⟨K,hKS,hK,hsmallK,hcard⟩ := Nat.find_spec hex
  refine ⟨K,hKS,hK,hsmallK,?_⟩
  intro A hAK hA
  by_contra! hsmallA
  have hmin := Nat.find_min' hex
    (show ∃ K : Finset V,K⊆S ∧ K.Nonempty ∧
      (G.edgeCut (K:Set V)).toFinset.card<k ∧ K.card=A.card from
        ⟨A,hAK.subset.trans hKS,hA,hsmallA,rfl⟩)
  have hlt := card_lt_card hAK
  omega

/-- Genuine basic finite multigraphs with two different connectivity islands
have a proper minimal deficient core of at least two actual vertices. All
quantification of basicness is over G's true vertex set, not its ambient type. -/
theorem native_exists_basic_small_core (G : Graph V E) {u v : G.vertexSet} {k : ℕ}
    (hsep : ¬FaultConnected G k u v)
    (hbasic : ∀ a : G.vertexSet,∃ b : G.vertexSet,a≠b ∧ FaultConnected G k a b) :
    ∃ K : Finset V,K⊂G.vertexSet.toFinset ∧ 2≤K.card ∧
      (G.edgeCut (K:Set V)).toFinset.card<k ∧
      (∀ a b : G.vertexSet,a.val∈K → FaultConnected G k a b → b.val∈K) ∧
      (∀ A : Finset V,A⊂K → A.Nonempty → k≤(G.edgeCut (A:Set V)).toFinset.card) := by
  classical
  rw [faultConnected_iff_cut_lower] at hsep
  push Not at hsep
  obtain ⟨S,hu,hv,hsmall⟩ := hsep
  let R : Finset V := (S∩G.vertexSet).toFinset
  have huR : u.val∈R := by simp [R,hu,u.property]
  have hsmallR : (G.edgeCut (R:Set V)).toFinset.card<k := by
    simpa [R,edgeCut_inter_vertexSet] using hsmall
  obtain ⟨K,hKR,hK,hsmallK,hmin⟩ := native_exists_minimal_small_cut G ⟨u.val,huR⟩ hsmallR
  have hactual : K⊆G.vertexSet.toFinset := by
    intro x hx
    have hr : x∈S∩G.vertexSet := by simpa [R] using hKR hx
    simpa using hr.2
  have hclosed : ∀ a b : G.vertexSet,a.val∈K → FaultConnected G k a b → b.val∈K := by
    intro a b ha hab
    exact native_small_cut_closed G hsmallK ha hab
  have hvK : v.val∉K := by
    intro hvK
    have hr : v.val∈S∩G.vertexSet := by simpa [R] using hKR hvK
    exact hv hr.1
  have hproper : K⊂G.vertexSet.toFinset := lt_of_le_of_ne hactual (by
    intro heq
    have hvG : v.val∈G.vertexSet.toFinset := by simp
    exact hvK ((congrArg (fun T : Finset V => v.val∈T) heq).mpr hvG))
  obtain ⟨a,ha⟩ := hK
  have haG : a∈G.vertexSet := by simpa using hactual ha
  obtain ⟨b,hab,hconn⟩ := hbasic ⟨a,haG⟩
  have hb := hclosed ⟨a,haG⟩ b ha hconn
  have hab' : a≠b.val := fun heq => hab (Subtype.ext heq)
  have htwo : 2≤K.card := by
    have hh : ({a,b.val}:Finset V)⊆K := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact ha
      · have heq := mem_singleton.mp hx
        subst x
        exact hb
    simpa [hab'] using card_le_card hh
  exact ⟨K,hproper,htwo,hsmallK,hclosed,hmin⟩
end LightEFTSpanners.MultigraphCuts
