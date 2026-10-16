import LightEFTSpanners.PartitionRefinementTermination
import Mathlib.Data.Fintype.Quotient

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Every partition of a nonempty finite actual vertex domain has genuine
surjective finite labels. Values on phantom ambient vertices are arbitrary and
do not add blocks or affect the equivalence on actual vertices. -/
theorem exists_actual_partition_labels (G : Graph V E) [Finite G.vertexSet]
    [Nonempty G.vertexSet] (R : Setoid G.vertexSet) :
    ∃ (m : ℕ) (f : V → Fin m),Function.Surjective (fun a : G.vertexSet => f a) ∧
      Setoid.ker (fun a : G.vertexSet => f a)=R := by
  classical
  let : Fintype (Quotient R) := Fintype.ofFinite (Quotient R)
  let q : G.vertexSet → Fin (Fintype.card (Quotient R)) :=
    fun a => (Fintype.equivFin (Quotient R)) (Quotient.mk R a)
  have hq : Function.Surjective q :=
    (Fintype.equivFin (Quotient R)).surjective.comp Quotient.mk_surjective
  let a0 : G.vertexSet := Classical.choice inferInstance
  let f : V → Fin (Fintype.card (Quotient R)) :=
    fun v => if h : v∈G.vertexSet then q ⟨v,h⟩ else q a0
  have hf : ∀ a : G.vertexSet,f a=q a := by
    intro a
    unfold f
    split
    · rfl
    · rename_i ha
      exact False.elim (ha a.property)
  refine ⟨Fintype.card (Quotient R),f,?_,?_⟩
  · intro i
    obtain ⟨a,ha⟩ := hq i
    exact ⟨a,(hf a).trans ha⟩
  · apply Setoid.ext
    intro a b
    change (f a=f b) ↔ R.r a b
    rw [hf a,hf b]
    constructor
    · intro h
      exact Quotient.exact ((Fintype.equivFin (Quotient R)).injective h)
    · intro h
      exact congrArg (Fintype.equivFin (Quotient R)) (Quotient.sound h)

/-- Actual least-color refinement iterates form an antitone sequence. -/
theorem color_refinement_iterates_antitone {X : Type*} {k : ℕ}
    (H : Fin k → SimpleGraph X) (R : Setoid X) :
    Antitone (fun n => (refinementStep H)^[n] R) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Function.iterate_succ_apply']
  exact refinementStep_le H _

/-- The actual terminal iterate admits finite occupied-block labels and every
color genuinely connects each fiber. Both termination and labels are constructed
here; neither a supplied terminal partition nor fiber connectivity is assumed. -/
theorem exists_native_terminal_labels (G : Graph V E) [Finite G.vertexSet]
    [Nonempty G.vertexSet] {k : ℕ} (color : E → Fin k) :
    let H : Fin k → SimpleGraph G.vertexSet := fun c => (G.restrict {e | color e=c}).toSimpleGraph
    ∃ N≤Nat.card G.vertexSet*Nat.card G.vertexSet,∃ (m : ℕ) (f : V → Fin m),
      Function.Surjective (fun a : G.vertexSet => f a) ∧
      Setoid.ker (fun a : G.vertexSet => f a)=(refinementStep H)^[N] ⊤ ∧
      (∀ c : Fin k,∀ a b : G.vertexSet,f a=f b →
        (blockGraph (H c) (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b) := by
  classical
  let : Fintype G.vertexSet := Fintype.ofFinite G.vertexSet
  intro H
  obtain ⟨N,hN,_,hfixed,_⟩ := stable_refinement_quadratic_bound H ⊤
  obtain ⟨m,f,hsurj,hker⟩ := exists_actual_partition_labels G ((refinementStep H)^[N] ⊤)
  refine ⟨N,by simpa only [Nat.card_eq_fintype_card] using hN,m,f,hsurj,hker,?_⟩
  intro c a b hab
  have hrel : ((refinementStep H)^[N] ⊤).r a b := by
    rw [← hker]
    exact hab
  have hr := (componentRefinement_eq_iff (H c) _).mp (hfixed c) a b hrel
  exact (congrArg (fun R : Setoid G.vertexSet => (blockGraph (H c) R).Reachable a b) hker).mpr hr
end LightEFTSpanners.MultigraphCuts
