import GreedyShortcuts.DirectedLift
import GreedyShortcuts.CanonicalSegments
import Mathlib.Data.Quot

/-! The actual strongly connected component quotient of an arbitrary finite
relation. Its representatives and condensation relation are constructed, and
the condensation is proved acyclic. -/
namespace GreedyShortcuts.SCCQuotient

open SimpleGraph DirectedPaths CanonicalSegments
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

def mutualSetoid (G : V → V → Prop) : Setoid V where
  r u v := Reachable G u v ∧ Reachable G v u
  iseqv := ⟨fun v => ⟨reachable_refl G v,reachable_refl G v⟩,
    fun h => h.symm,fun h₁ h₂ => ⟨reachable_trans h₁.1 h₂.1,reachable_trans h₂.2 h₁.2⟩⟩

abbrev Component (G : V → V → Prop) := Quotient (mutualSetoid G)

noncomputable instance componentDecidableEq (G : V → V → Prop) : DecidableEq (Component G) :=
  Classical.decEq _

noncomputable instance componentFintype (G : V → V → Prop) : Fintype (Component G) :=
  Fintype.ofSurjective (Quotient.mk (mutualSetoid G)) Quotient.mk_surjective

def component (G : V → V → Prop) (v : V) : Component G := Quotient.mk (mutualSetoid G) v

noncomputable def representative (G : V → V → Prop) (c : Component G) : V := c.out

theorem representative_mutual (G : V → V → Prop) (v : V) :
    Reachable G (representative G (component G v)) v ∧
    Reachable G v (representative G (component G v)) := Quotient.mk_out (s := mutualSetoid G) v

theorem representative_injective (G : V → V → Prop) : Function.Injective (representative G) :=
  Quotient.out_injective

theorem component_card (G : V → V → Prop) : Fintype.card (Component G) ≤ Fintype.card V :=
  Fintype.card_le_of_injective _ (representative_injective G)

/-- An actual original edge between components, rather than their transitive
closure: this is essential for the later constant-hop lifting bound. -/
def graph (G : V → V → Prop) (a b : Component G) : Prop :=
  ∃ u v,G u v ∧ component G u = a ∧ component G v = b

theorem edge_lift (G : V → V → Prop) {a b : Component G} (hab : graph G a b) :
    Reachable G (representative G a) (representative G b) := by
  obtain ⟨u,v,huv,rfl,rfl⟩ := hab
  exact reachable_trans (representative_mutual G u).1
    (reachable_trans (reachable_edge huv) (representative_mutual G v).2)

theorem reachable_lift (G : V → V → Prop) {a b : Component G} (hab : Reachable (graph G) a b) :
    Reachable G (representative G a) (representative G b) :=
  DirectedLift.reachable (representative G) (fun _ _ => edge_lift G) hab

theorem acyclic (G : V → V → Prop) : Acyclic (graph G) := by
  apply (acyclic_iff_reachable_antisymm _).mpr
  intro a b hab hba
  exact Quotient.out_equiv_out.mp ⟨reachable_lift G hab,reachable_lift G hba⟩

theorem reachable_project (G : V → V → Prop) {s t : V} (hr : Reachable G s t) :
    Reachable (graph G) (component G s) (component G t) :=
  DirectedLift.reachable (component G)
    (fun u v huv => reachable_edge ⟨u,v,huv,rfl,rfl⟩) hr

theorem reachable_iff (G : V → V → Prop) (s t : V) :
    Reachable (graph G) (component G s) (component G t) ↔ Reachable G s t := by
  constructor
  · intro h
    exact reachable_trans (representative_mutual G s).2
      (reachable_trans (reachable_lift G h) (representative_mutual G t).1)
  · exact reachable_project G

end GreedyShortcuts.SCCQuotient
