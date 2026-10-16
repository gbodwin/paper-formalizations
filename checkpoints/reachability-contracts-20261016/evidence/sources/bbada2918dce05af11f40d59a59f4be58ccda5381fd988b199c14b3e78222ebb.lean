import SlackSparsification.ReachabilityBasics
import SlackSparsification.ReachabilityParameters
import SlackSparsification.DirectedPreserver

/-! Explicit remaining premises for the directed reachability reduction.
These results do not construct the sourcewise preserver or the half-cover. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Both orientations are needed: an A-only sourcewise hypothesis does not
supply a sourcewise theorem on reversed arcs. -/
def BidirectionalSourcewiseBound (K : SimpleGraph V) (A : V → V → Prop) (C : ℝ) : Prop :=
  SourcewiseBound K A C ∧ SourcewiseBound K (fun u v => A v u) C

omit [Fintype V] [DecidableEq V] in
theorem reachable_filter_ambient (K : SimpleGraph V) (F : Finset (V × V)) (s t : V) :
    Reachable K (edgeRel (F.filter fun e => K.Adj e.1 e.2)) s t ↔
      Reachable K (edgeRel F) s t := by
  constructor
  · exact reachable_mono (fun _ _ h => (mem_filter.mp h).1)
  · rintro ⟨p, hp⟩
    exact ⟨p, fun d hd => mem_filter.mpr ⟨hp d hd, d.adj⟩⟩

omit [DecidableEq V] in
/-- Sourcewise witnesses can be normalized to actual input arcs with no cost. -/
theorem sourcewise_input {K : SimpleGraph V} {A : V → V → Prop} {C : ℝ}
    (hs : SourcewiseBound K A C) (R : Finset V) (P : Finset (V × V))
    (hR : ∀ st ∈ P, st.1 ∈ R) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
      (F.card : ℝ) ≤ C * (Real.sqrt (Fintype.card V * (P.card : ℝ) * R.card) + Fintype.card V) ∧
      ∀ st ∈ P, (Reachable K (edgeRel F) st.1 st.2 ↔ Reachable K A st.1 st.2) := by
  obtain ⟨F, hFA, hc, hs⟩ := hs R P hR
  refine ⟨F.filter (fun e => K.Adj e.1 e.2), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨he, hK⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, hK, hFA e he⟩
  · exact (show ((F.filter fun e => K.Adj e.1 e.2).card : ℝ) ≤ F.card by
      exact_mod_cast card_filter_le F _).trans hc
  · intro st hst
    rw [reachable_filter_ambient]
    exact ⟨reachable_mono (fun u v h => hFA (u,v) h), hs st hst⟩

/-- Reversing the sourcewise witness supplies the targetwise orientation.
Repeated ordered pairs are handled by image cardinality, not summed twice. -/
theorem targetwise_indexed {D : Type*} [DecidableEq D] {K : SimpleGraph V}
    {A : V → V → Prop} {C : ℝ} (hC : 0 ≤ C)
    (hs : SourcewiseBound K (fun u v => A v u) C)
    (R : Finset V) (P : Finset D) (src dst : D → V) (hR : ∀ i ∈ P, dst i ∈ R) :
    ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧
      (F.card : ℝ) ≤ C * (Real.sqrt (Fintype.card V * (P.card : ℝ) * R.card) + Fintype.card V) ∧
      ∀ i ∈ P, Reachable K A (src i) (dst i) → Reachable K (edgeRel F) (src i) (dst i) := by
  obtain ⟨F, hFA, hc, hs⟩ := sourcewise_indexed hC hs R P dst src hR
  refine ⟨F.image Prod.swap, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, hxe⟩ := mem_image.mp he
    rw [← hxe]
    exact hFA x hx
  · exact (show ((F.image Prod.swap).card : ℝ) ≤ F.card by
      exact_mod_cast card_image_le).trans hc
  · intro i hi hreach
    have hr := hs i hi (reachable_reverse.mpr hreach)
    have hr' : Reachable K (fun u v => edgeRel (F.image Prod.swap) v u) (dst i) (src i) :=
      reachable_mono (fun u v h => mem_image.mpr ⟨(u,v),h,rfl⟩) hr
    exact reachable_reverse.mp hr'

/-- Explicit missing combinatorial half-cover, already restricted to input arcs.
Numerical optimization alone does not provide this witness. -/
def ReachabilityHalfCover (K : SimpleGraph V) (A : V → V → Prop) (B : ℝ)
    (threshold : ℕ) : Prop :=
  ∀ Q : Finset (V × V), threshold < Q.card →
    ∃ (F R : Finset (V × V)), F ⊆ inputArcs K A ∧ R ⊆ Q ∧
      (R.card : ℝ) ≤ (1 / 2 : ℝ) * Q.card ∧
      (F.card : ℝ) ≤ B * (Q.card : ℝ) ^ (2 / 3 : ℝ) ∧
      ∀ st ∈ Q \ R, Reachable K A st.1 st.2 → Reachable K (edgeRel F) st.1 st.2

/-- Conditional amplification with exactly the two unproved construction
obligations exposed. No supplied paths or reachability of every demand is required. -/
theorem reachability_complete_of_constructors (K : SimpleGraph V) (A : V → V → Prop)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (threshold : ℕ)
    (ht : threshold ^ 2 ≤ Fintype.card V) (hs : SourcewiseBound K A C)
    (hhalf : ReachabilityHalfCover K A B threshold) (P : Finset (V × V)) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
      (F.card : ℝ) ≤ 2 * C * Fintype.card V +
        B / (1 - (1 / 2 : ℝ) ^ (2 / 3 : ℝ)) * (P.card : ℝ) ^ (2 / 3 : ℝ) ∧
      ∀ st ∈ P, (Reachable K (edgeRel F) st.1 st.2 ↔ Reachable K A st.1 st.2) := by
  let Sat := fun (F : Finset (V × V)) (st : V × V) =>
    Reachable K A st.1 st.2 → Reachable K (edgeRel F) st.1 st.2
  have hmono : ∀ F J, F ⊆ J → ∀ st, Sat F st → Sat J st := by
    intro F J h st hs hr
    exact reachable_mono (fun _ _ he => h he) (hs hr)
  have hsmall : ∀ Q : Finset (V × V), Q.card ≤ threshold →
      ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
        (F.card : ℝ) ≤ 2 * C * Fintype.card V ∧ ∀ st ∈ Q, Sat F st := by
    intro Q hQ
    have hq : Q.card ^ 2 ≤ Fintype.card V := (Nat.pow_le_pow_left hQ 2).trans ht
    obtain ⟨F, hFA, hc, hsat⟩ := exists_reachability_small hC hs Q Prod.fst Prod.snd hq
    refine ⟨F.filter (fun e => K.Adj e.1 e.2), ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨he,hK⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨mem_univ _,hK,hFA e he⟩
    · exact (show ((F.filter fun e => K.Adj e.1 e.2).card : ℝ) ≤ F.card by
        exact_mod_cast card_filter_le F _).trans hc
    · intro st hst hr
      exact (reachable_filter_ambient K F _ _).mpr (hsat st hst hr)
  obtain ⟨F, hF, hc, hsat⟩ := complete_of_slack (inputArcs K A) Sat hmono
    (2 * C * Fintype.card V) B (1/2) (2/3) (by positivity) hB
    (by norm_num) (by norm_num) (by norm_num) threshold hsmall hhalf P
  refine ⟨F,hF,hc,fun st hst => ⟨?_,hsat st hst⟩⟩
  exact reachable_mono (fun u v he => (mem_filter.mp (hF he)).2.2)
end SlackSparsification.Directed
