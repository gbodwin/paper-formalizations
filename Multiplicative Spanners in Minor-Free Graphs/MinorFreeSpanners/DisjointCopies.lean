import MinorFreeSpanners.MinorRestriction
import MinorFreeSpanners.GirthComponents
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Actual disjoint copies for the conditional lower-bound construction.
The number of copies is represented by an arbitrary finite index type. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {J V : Type*}

def copyGraph (J : Type*) (G : SimpleGraph V) : SimpleGraph (J × V) where
  Adj u v := u.1 = v.1 ∧ G.Adj u.2 v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.ne rfl⟩

namespace copyGraph
variable {G : SimpleGraph V}

def projection : copyGraph J G →g G where
  toFun := Prod.snd
  map_rel' := fun h => h.2

def inclusion (j : J) : G →g copyGraph J G where
  toFun := fun v => (j,v)
  map_rel' := fun h => ⟨rfl,h⟩

theorem first_eq_of_walk {u v : J × V} (p : (copyGraph J G).Walk u v) :
    u.1 = v.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact h.1.trans ih

theorem first_eq_of_reachable {u v : J × V}
    (h : (copyGraph J G).Reachable u v) : u.1 = v.1 := by
  obtain ⟨p⟩ := h
  exact first_eq_of_walk p

/-- Projection to the original graph is injective on each actual connected
component, although it is not injective on the whole disjoint union. -/
theorem component_projection_injective (C : (copyGraph J G).ConnectedComponent) :
    Function.Injective (fun v : C => v.val.2) := by
  intro u v huv
  apply Subtype.ext
  exact Prod.ext (first_eq_of_reachable (C.reachable_of_mem_supp u.property v.property)) huv

def componentProjection (C : (copyGraph J G).ConnectedComponent) :
    C.toSimpleGraph →g G :=
  projection.comp (Embedding.induce C.supp).toHom

/-- Taking arbitrarily many disjoint copies preserves clique-minor
exclusion. No bound on the total edge count of the union is required. -/
theorem minorFree (h : ℕ) (hh : 0 < h) (hG : CliqueMinorFree G h) :
    CliqueMinorFree (copyGraph J G) h := by
  apply cliqueMinorFree_of_components _ h hh
  intro C hM
  obtain ⟨M⟩ := hM
  exact hG ⟨M.mapHost (componentProjection C) (component_projection_injective C)⟩

/-- Disjoint copies preserve the actual simple-cycle girth bound. -/
theorem girth {r : ℕ} (hG : GirthAbove G r) : GirthAbove (copyGraph J G) r := by
  apply GirthAbove.of_components
  intro C
  exact hG.of_embedding (componentProjection C) (component_projection_injective C)

/-- Bijection between oriented edges of the union and an index together
with an oriented edge of the original graph. -/
def dartEquiv : (copyGraph J G).Dart ≃ J × G.Dart where
  toFun d := ⟨d.fst.1,⟨(d.fst.2,d.snd.2),d.adj.2⟩⟩
  invFun d := ⟨((d.1,d.2.fst),(d.1,d.2.snd)),⟨rfl,d.2.adj⟩⟩
  left_inv d := by
    apply Dart.ext
    apply Prod.ext
    · rfl
    · exact Prod.ext d.adj.1 rfl
  right_inv d := by cases d; rfl

variable [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem edge_count (G : SimpleGraph V) :
    (copyGraph J G).edgeFinset.card = Fintype.card J * G.edgeFinset.card := by
  have he := Fintype.card_congr (@dartEquiv J V G)
  rw [Fintype.card_prod, dart_card_eq_twice_card_edges,
    dart_card_eq_twice_card_edges] at he
  nlinarith [he]

end copyGraph

variable [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Exact finite construction behind the lower-bound copying step. The
existence of a suitable dense core is intentionally not asserted here. -/
theorem copied_core_lower_bound (G : SimpleGraph V) (k h : ℕ) (hh : 0 < h)
    (hm : G.edgeFinset.card < h.choose 2) (hg : GirthAbove G (2*k)) :
    CliqueMinorFree (copyGraph J G) h ∧
    ∀ H : SimpleGraph (J × V),
      LightSpanners.IsSpanner (copyGraph J G) H (fun _ => 1) (2*k-1) →
      H = copyGraph J G ∧ H.edgeFinset.card = Fintype.card J * G.edgeFinset.card := by
  refine ⟨copyGraph.minorFree h hh (cliqueMinorFree_of_edges G h hm), ?_⟩
  intro H hH
  have he := high_girth_spanner_eq k (copyGraph.girth hg) hH
  subst H
  exact ⟨rfl,copyGraph.edge_count G⟩

end MinorFreeSpanners
