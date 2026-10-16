import SlackSparsification.SCCQuotient
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum

namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped BigOperators NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def componentVertices (K : SimpleGraph V) (A : V → V → Prop) (c : Component K A) : Set V :=
  {v | component K A v = c}

omit [Fintype V] [DecidableEq V] in
theorem allowed_map_iff {W : Type*} {K : SimpleGraph V} {L : SimpleGraph W}
    (f : K →g L) {s t : V} (p : K.Walk s t) (B : W → W → Prop) :
    Allowed B (p.map f) ↔ Allowed (fun u v => B (f u) (f v)) p := by
  simp [Allowed,Walk.darts_map]

/-- Any two vertices in an SCC are joined inside its induced ambient graph. -/
theorem component_induced_reachable (K : SimpleGraph V) (A : V → V → Prop)
    (c : Component K A) (x y : componentVertices K A c) :
    Reachable (K.induce (componentVertices K A c)) (fun u v => A u.val v.val) x y := by
  have heq : component K A x.val = component K A y.val := x.property.trans y.property.symm
  obtain ⟨p,hp⟩ := ((component_eq_iff K A x.val y.val).mp heq).1
  have hsupport : ∀ v ∈ p.support, v ∈ componentVertices K A c := by
    intro v hv
    exact (support_same_component K A p hp heq hv).trans x.property
  let q := p.induce (componentVertices K A c) hsupport
  have hq : Allowed (fun u v : componentVertices K A c => A u.val v.val) q := by
    apply (allowed_map_iff (SimpleGraph.Embedding.induce (componentVertices K A c)).toHom q A).mp
    simpa [q] using hp
  exact ⟨q,hq⟩

/-- Actual original-arc connector for one SCC, charged to its own vertex count. -/
theorem exists_component_connector (K : SimpleGraph V) (A : V → V → Prop)
    (c : Component K A) :
    ∃ E : Finset (V × V), E ⊆ inputArcs K A ∧
      E.card ≤ 2 * Fintype.card (componentVertices K A c) ∧
      ∀ x y, component K A x = c → component K A y = c → Reachable K (edgeRel E) x y := by
  classical
  let W := componentVertices K A c
  let L := K.induce W
  let B := fun u v : W => A u.val v.val
  let r : W := ⟨c.out,Quotient.out_eq c⟩
  obtain ⟨F,hFc,hFA,hFd⟩ := exists_root_preserver L B (fun _ _ => 0) r
  have hreach : ∀ x y : W, Reachable L (edgeRel F) x y := by
    intro x y
    have hx : distance L B (fun _ _ => 0) x r ≠ ⊤ :=
      (distance_ne_top_iff L B _ x r).mpr (component_induced_reachable K A c x r)
    have hy : distance L B (fun _ _ => 0) r y ≠ ⊤ :=
      (distance_ne_top_iff L B _ r y).mpr (component_induced_reachable K A c r y)
    have hx' : Reachable L (edgeRel F) x r := (distance_ne_top_iff L (edgeRel F) _ x r).mp
      (by rwa [(hFd x).2])
    have hy' : Reachable L (edgeRel F) r y := (distance_ne_top_iff L (edgeRel F) _ r y).mp
      (by rwa [(hFd y).1])
    exact reachable_trans hx' hy'
  let J := F.filter fun e => L.Adj e.1 e.2
  let E := J.image fun e => (e.1.val,e.2.val)
  refine ⟨E,?_,?_,?_⟩
  · intro e he
    obtain ⟨uv,huv,rfl⟩ := mem_image.mp he
    obtain ⟨huv,hadj⟩ := mem_filter.mp huv
    exact mem_filter.mpr ⟨mem_univ _,hadj,hFA uv huv⟩
  · exact card_image_le.trans ((card_filter_le F _).trans hFc)
  · intro x y hx hy
    let x' : W := ⟨x,hx⟩
    let y' : W := ⟨y,hy⟩
    have hJ : Reachable L (edgeRel J) x' y' := (reachable_filter_ambient L F x' y').mpr (hreach x' y')
    obtain ⟨p,hp⟩ := hJ
    refine ⟨p.map (SimpleGraph.Embedding.induce W).toHom,?_⟩
    apply (allowed_map_iff _ p (edgeRel E)).mpr
    intro d hd
    exact mem_image.mpr ⟨(d.fst,d.snd),hp d hd,rfl⟩

/-- The finite SCC fibers partition the original vertices, including n=0. -/
theorem component_fiber_card_sum (K : SimpleGraph V) (A : V → V → Prop) :
    (∑ c : Component K A, Fintype.card (componentVertices K A c)) = Fintype.card V := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (component K A))
  calc
    (∑ c : Component K A, Fintype.card (componentVertices K A c)) =
        ∑ c : Component K A, Fintype.card {x // component K A x = c} := by
      apply sum_congr rfl
      intro c _
      exact Fintype.card_congr (Equiv.refl _)
    _ = Fintype.card V := by simpa only [Fintype.card_sigma] using h

/-- Construct all internal connectors with a total 2n budget, not 2n per SCC. -/
theorem exists_internal_connector (K : SimpleGraph V) (A : V → V → Prop) :
    ∃ I : Finset (V × V), I ⊆ inputArcs K A ∧ I.card ≤ 2 * Fintype.card V ∧
      ∀ x y, component K A x = component K A y → Reachable K (edgeRel I) x y := by
  classical
  choose E hEA hEc hEr using exists_component_connector K A
  let I := (univ : Finset (Component K A)).biUnion E
  refine ⟨I,?_,?_,?_⟩
  · intro e he
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp he
    exact hEA c hc
  · calc
      I.card ≤ ∑ c : Component K A, (E c).card := card_biUnion_le
      _ ≤ ∑ c : Component K A, 2 * Fintype.card (componentVertices K A c) :=
        sum_le_sum (fun c _ => hEc c)
      _ = 2 * Fintype.card V := by rw [← mul_sum,component_fiber_card_sum]
  · intro x y hxy
    apply reachable_mono (fun _ _ h => mem_biUnion.mpr ⟨component K A x,mem_univ _,h⟩)
    exact hEr (component K A x) x y rfl hxy.symm

/-- Uniform sourcewise construction for every finite orientation; no SCC,
acyclicity, internal connector or sourcewise-existence premise remains. -/
theorem sourcewise_bound_uniform (K : SimpleGraph V) (A : V → V → Prop) : SourcewiseBound K A 4 := by
  obtain ⟨I,hIA,hIc,hI⟩ := exists_internal_connector K A
  exact sourcewise_bound_of_internal_connector K A I hIA hIc hI

theorem bidirectional_sourcewise_uniform (K : SimpleGraph V) (A : V → V → Prop) :
    BidirectionalSourcewiseBound K A 4 := by
  exact ⟨sourcewise_bound_uniform K A,sourcewise_bound_uniform K (fun u v => A v u)⟩

/-- Unconditional finite directed reachability preserver on actual input arcs.
No sourcewise or connector premise remains; empty inputs are permitted. -/
theorem exists_reachability_preserver (K : SimpleGraph V) (A : V → V → Prop)
    (P : Finset (V × V)) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
      (F.card : ℝ) ≤ 8 * Fintype.card V +
        (25 * (Fintype.card V : ℝ) ^ (2/3 : ℝ)) /
          (1 - (1/2 : ℝ) ^ (2/3 : ℝ)) * (P.card : ℝ) ^ (2/3 : ℝ) ∧
      ∀ st ∈ P, (Reachable K (edgeRel F) st.1 st.2 ↔ Reachable K A st.1 st.2) := by
  have h := reachability_complete_sourcewise K A 4 (by norm_num)
    (bidirectional_sourcewise_uniform K A) P
  norm_num at h ⊢
  exact h

end SlackSparsification.Directed
