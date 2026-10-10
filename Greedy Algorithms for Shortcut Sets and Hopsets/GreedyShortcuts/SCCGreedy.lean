import GreedyShortcuts.SCCStars
import GreedyShortcuts.DAGAllTargets

/-! The checked DAG greedy theorem applied to the actual SCC condensation.
This proves the large-budget preprocessing stage of Section 3.3. The separate
small-budget kernel reduction is not assumed or claimed here. -/
namespace GreedyShortcuts.SCCGreedy

open Finset DirectedPaths SCCQuotient
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def output (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) : Finset (V × V) :=
  lifted G (GraphGreedy.output (graph G) β hβ)

theorem output_legal (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    output G β hβ ⊆ candidates G :=
  lifted_legal G (GraphGreedy.output_subset (graph G) β hβ)

theorem output_reachable_iff (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) (s t : V) :
    Reachable (augment G (output G β hβ)) s t ↔ Reachable G s t :=
  reachable_augment_iff G _ (output_legal G β hβ) s t

theorem output_hop_bound (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    {s t : V} (hr : Reachable G s t) : hopDist (augment G (output G β hβ)) s t ≤ 3*β+2 :=
  lifted_hop_bound G _ β (fun _ _ => GraphGreedy.output_hop_bound (graph G) β hβ) hr

theorem output_card_le (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    (output G β hβ).card ≤ 2*Fintype.card V + (GraphGreedy.output (graph G) β hβ).card :=
  lifted_card G _

/-- Exact source-shaped quantitative application, with the actual number of
components q and the explicitly charged preprocessing cost 2n. -/
theorem output_card_log_bound (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    (hq : 2 ≤ Fintype.card (Component G)) :
    ((output G β hβ).card : ℝ) ≤ 2*(Fintype.card V:ℝ) +
      4*Real.logb 2 (Fintype.card (Component G):ℝ) *
        (16385*(Fintype.card (Component G):ℝ)^(3/(2:ℝ))/(β:ℝ)^(3/(2:ℝ)) +
          147456*(Fintype.card (Component G):ℝ)^2/(β:ℝ)^3) := by
  have hc : ((output G β hβ).card:ℝ) ≤ 2*(Fintype.card V:ℝ) +
      ((GraphGreedy.output (graph G) β hβ).card:ℝ) := by
    exact_mod_cast output_card_le G β hβ
  exact hc.trans (add_le_add (le_refl _) (DAGAllTargets.output_card_log_bound (acyclic G) β hβ hq))

theorem output_card_of_one_component (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    (hq : Fintype.card (Component G) ≤ 1) : (output G β hβ).card ≤ 2*Fintype.card V := by
  have he := DAGAllTargets.output_empty_of_card_le (graph G) β hβ (hq.trans hβ)
  simpa only [he,Finset.card_empty,Nat.add_zero] using output_card_le G β hβ

/-- Exact integer retargeting removes the constant-factor hop inflation. -/
theorem target_hop_bound (G : V → V → Prop) (B : ℕ) (hB : 5 ≤ B)
    {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (output G ((B-2)/3) (by omega))) s t ≤ B :=
  (output_hop_bound G ((B-2)/3) (by omega) hr).trans (by omega)

end GreedyShortcuts.SCCGreedy
