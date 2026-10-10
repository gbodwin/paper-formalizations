import LightEFTSpanners.ConnectivityCuts

namespace LightEFTSpanners.ConnectivityCuts
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- A cut smaller than k is a union of native k-edge-connectivity classes. -/
theorem small_cut_closed (G : SimpleGraph V) {S : Set V} {k : ℕ}
    (hsmall : (edges G S).card<k) {a b : V} (ha : a∈S)
    (hconn : G.IsEdgeReachable k a b) : b∈S := by
  by_contra hb
  exact (not_lt_of_ge (edgeReachable_le_cut G S hconn ha hb)) hsmall

/-- Failure of native edge connectivity produces an actual separating small
vertex cut, rather than an assumed numerical cut oracle. -/
theorem exists_small_separating_cut (G : SimpleGraph V) {a b : V} {k : ℕ}
    (h : ¬G.IsEdgeReachable k a b) :
    ∃ S : Set V,a∈S ∧ b∉S ∧ (edges G S).card<k := by
  rw [edgeReachable_iff_cut_lower] at h
  push Not at h
  exact h

/-- A nonempty finite small-cut set has an inclusion-minimal nonempty
small-cut subset; every proper nonempty inner subset has cut at least k. -/
theorem exists_minimal_small_cut (G : SimpleGraph V) {S : Finset V} {k : ℕ}
    (hS : S.Nonempty) (hsmall : (edges G (S:Set V)).card<k) :
    ∃ K : Finset V,K⊆S ∧ K.Nonempty ∧ (edges G (K:Set V)).card<k ∧
      ∀ A : Finset V,A⊂K → A.Nonempty → k≤(edges G (A:Set V)).card := by
  classical
  have hex : ∃ n : ℕ, ∃ K : Finset V,
      K⊆S ∧ K.Nonempty ∧ (edges G (K:Set V)).card<k ∧ K.card=n :=
    ⟨S.card,S,Subset.rfl,hS,hsmall,rfl⟩
  obtain ⟨K,hKS,hK,hsmallK,hcard⟩ := Nat.find_spec hex
  refine ⟨K,hKS,hK,hsmallK,?_⟩
  intro A hAK hA
  by_contra! hsmallA
  have hmin := Nat.find_min' hex
    (show ∃ K : Finset V,K⊆S ∧ K.Nonempty ∧ (edges G (K:Set V)).card<k ∧ K.card=A.card from
      ⟨A,hAK.subset.trans hKS,hA,hsmallA,rfl⟩)
  have hlt := Finset.card_lt_card hAK
  omega

/-- In a basic packing instance (every vertex has a distinct k-connected
partner), two different connectivity islands yield a proper small-cut core
with at least two vertices and no smaller nonempty deficient subset. This is
the actual finite selection step; contraction and forest existence are separate. -/
theorem exists_basic_small_core (G : SimpleGraph V) {u v : V} {k : ℕ}
    (hsep : ¬G.IsEdgeReachable k u v)
    (hbasic : ∀ a : V,∃ b : V,a≠b ∧ G.IsEdgeReachable k a b) :
    ∃ K : Finset V,K⊂univ ∧ 2≤K.card ∧ (edges G (K:Set V)).card<k ∧
      (∀ a∈K,∀ b,G.IsEdgeReachable k a b → b∈K) ∧
      (∀ A : Finset V,A⊂K → A.Nonempty → k≤(edges G (A:Set V)).card) := by
  classical
  obtain ⟨S,hu,hv,hsmall⟩ := exists_small_separating_cut G hsep
  obtain ⟨K,hKS,hK,hsmallK,hmin⟩ := exists_minimal_small_cut G
    (show S.toFinset.Nonempty from ⟨u,by simpa using hu⟩)
    (by simpa using hsmall)
  have hclosed : ∀ a∈K,∀ b,G.IsEdgeReachable k a b → b∈K := by
    intro a ha b hab
    exact small_cut_closed G hsmallK ha hab
  have hvK : v∉K := fun h => hv (by simpa using hKS h)
  have hproper : K⊂univ := lt_of_le_of_ne (subset_univ K)
    (fun heq => hvK (heq ▸ mem_univ v))
  obtain ⟨a,ha⟩ := hK
  obtain ⟨b,hab,hconn⟩ := hbasic a
  have hb := hclosed a ha b hconn
  have htwo : 2≤K.card := by
    have hh : ({a,b}:Finset V)⊆K := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact ha
      · have heq := mem_singleton.mp hx
        subst x
        exact hb
    simpa [hab] using card_le_card hh
  exact ⟨K,hproper,htwo,hsmallK,hclosed,hmin⟩
end LightEFTSpanners.ConnectivityCuts
