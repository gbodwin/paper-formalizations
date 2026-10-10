import GreedyShortcuts.ChainExcessSharp

/-! Source support of the same raw-greedy excess account. These finite regime
bounds require an explicit source-mass inequality; uniform chain sizes alone
do not imply that inequality or universal cubic progress. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset ChainFirst DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def unsaturatedSources (H : Finset (V × V)) : Finset V :=
  (T.unsaturated H).image Prod.fst

theorem unsaturatedSources_antitone : Antitone T.unsaturatedSources := by
  classical
  intro H J hHJ
  exact Finset.image_subset_image (T.unsaturated_antitone hHJ)

/-- Each actual unsaturated source contributes at most one earliest-entry
important demand per chain. No positive source multiplicity is assumed. -/
theorem unsaturated_card_le_sources (H : Finset (V × V)) :
    (T.unsaturated H).card ≤ (T.unsaturatedSources H).card*Fintype.card I := by
  classical
  let pairs := (T.unsaturatedSources H) ×ˢ (Finset.univ : Finset I)
  have hin : T.unsaturated H ⊆ pairs.image (fun sc => (sc.1,entry T.chains sc.1 sc.2)) := by
    intro st hst
    have hi := (Finset.mem_filter.mp hst).1
    obtain ⟨sc,hsc,he⟩ := Finset.mem_image.mp hi
    apply Finset.mem_image.mpr
    refine ⟨sc,Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,he⟩
    have hs : st.1 ∈ T.unsaturatedSources H := Finset.mem_image.mpr ⟨st,hst,rfl⟩
    have he₁ := congrArg Prod.fst he
    dsimp only [Prod.fst] at he₁
    exact he₁.symm ▸ hs
  calc
    _ ≤ (pairs.image (fun sc => (sc.1,entry T.chains sc.1 sc.2))).card :=
      Finset.card_le_card hin
    _ ≤ pairs.card := Finset.card_image_le
    _ = _ := by simp [pairs]

/-- Actual output bound using the initially unsaturated source support. -/
theorem output_card_sources (D : ℕ) (hD : 3 ≤ D) :
    (T.output D (by omega)).card ≤
      2*(25*((T.unsaturatedSources ∅).card*Fintype.card I)/D+1) := by
  have hu := T.unsaturated_card_le_sources ∅
  have hd : 25*(T.unsaturated ∅).card/D ≤
      25*((T.unsaturatedSources ∅).card*Fintype.card I)/D :=
    Nat.div_le_div_right (Nat.mul_le_mul_left 25 hu)
  exact (T.output_card_unsaturated_sharp D hD).trans (by omega)

/-- An explicit source-mass regime gives linear greedy size. This theorem
neither assumes nor concludes a universal cubic per-step saving. -/
theorem output_card_linear_of_source_mass (D b : ℕ) (hD : 3 ≤ D)
    (hmass : (T.unsaturatedSources ∅).card*Fintype.card I ≤ b*Fintype.card V*D) :
    (T.output D (by omega)).card ≤ 50*b*Fintype.card V+2 := by
  have ho := T.output_card_sources D hD
  have hq := Nat.div_mul_le_self (25*((T.unsaturatedSources ∅).card*Fintype.card I)) D
  have hm := Nat.mul_le_mul_left 25 hmass
  have hd : 25*((T.unsaturatedSources ∅).card*Fintype.card I)/D ≤ 25*b*Fintype.card V := by
    nlinarith
  nlinarith

/-- An existing direct important edge already attains the exact endpoint
floor, including equal labels and uncovered endpoints. -/
theorem direct_base_saturated (H : Finset (V × V)) {s t : V}
    (hst : (s,t) ∈ T.important) (hdirect : s=t ∨ T.G s t) :
    T.distance H s t = T.endpointFloor s t := by
  classical
  apply Nat.le_antisymm _ (T.endpointFloor_le_distance H (T.important_spec hst).1)
  by_cases he : s=t
  · subst t
    have hh := T.distance_le_walk H (T.important_spec hst).1 .nil (allowed_nil _ _)
    simpa [count,chainSet,endpointFloor] using hh
  · have hg : T.G s t := hdirect.resolve_left he
    let p : DWalk s t := .cons (by simpa using he) .nil
    have hp : Allowed (T.graph H s) p := by
      change Allowed (T.graph H s) (SimpleGraph.Walk.cons _ SimpleGraph.Walk.nil)
      rw [allowed_cons]
      exact ⟨⟨Or.inl hg,Or.inr (Or.inr (T.important_spec hst).2)⟩,allowed_nil _ _⟩
    have hh := T.distance_le_walk H (T.important_spec hst).1 p hp
    simpa [p,count,chainSet,endpointFloor] using hh

/-- A concrete original-edge certificate excludes whole rows from the actual
unsaturated source support. It does not alter the raw objective. -/
theorem unsaturatedSources_subset_of_direct (C : Finset V)
    (hC : ∀ s∉C,∀ t,(s,t)∈T.important → s=t ∨ T.G s t) :
    T.unsaturatedSources ∅ ⊆ C := by
  classical
  intro s hs
  obtain ⟨st,hst,hsource⟩ := Finset.mem_image.mp hs
  by_contra hn
  have hp := (Finset.mem_filter.mp hst).1
  have hd := (Finset.mem_filter.mp hst).2
  have he := T.direct_base_saturated ∅ hp (hC st.1 (by simpa only [hsource] using hn) st.2 hp)
  omega

/-- The same final raw-greedy output with a finite original-edge source
certificate. The certificate is a checkable graph property, not a progress law. -/
theorem output_card_source_certificate (D : ℕ) (hD : 3 ≤ D) (C : Finset V)
    (hC : ∀ s∉C,∀ t,(s,t)∈T.important → s=t ∨ T.G s t) :
    (T.output D (by omega)).card ≤ 2*(25*(C.card*Fintype.card I)/D+1) := by
  have hs := Finset.card_le_card (T.unsaturatedSources_subset_of_direct C hC)
  have hm := Nat.mul_le_mul_left 25 (Nat.mul_le_mul_right (Fintype.card I) hs)
  have hd : 25*((T.unsaturatedSources ∅).card*Fintype.card I)/D ≤
      25*(C.card*Fintype.card I)/D := Nat.div_le_div_right hm
  exact (T.output_card_sources D hD).trans (by omega)

/-- Uniform-size arithmetic for the explicit certificate regime. The
original-edge row certificate and its cardinality premise remain visible. -/
theorem output_card_uniform_source_certificate (D b : ℕ) (hD : 3 ≤ D)
    (C : Finset V)
    (hC : ∀ s∉C,∀ t,(s,t)∈T.important → s=t ∨ T.G s t)
    (hsmall : C.card ≤ b*Fintype.card I)
    (hchains : Fintype.card I ≤ D^2)
    (hsize : Fintype.card V = Fintype.card I*D) :
    (T.output D (by omega)).card ≤ 50*b*Fintype.card V+2 := by
  apply T.output_card_linear_of_source_mass D b hD
  have hs := Finset.card_le_card (T.unsaturatedSources_subset_of_direct C hC)
  calc
    _ ≤ (b*Fintype.card I)*Fintype.card I :=
      Nat.mul_le_mul_right _ (hs.trans hsmall)
    _ ≤ (b*Fintype.card I)*D^2 := Nat.mul_le_mul_left _ hchains
    _ = b*Fintype.card V*D := by rw [hsize];ring

end GreedyShortcuts.ChainDistance.Context
