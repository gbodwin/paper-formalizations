import GreedyShortcuts.ChainImportantPairs
import GreedyShortcuts.FiniteThresholdGreedy

/-! Actual raw-sum chain greedy, with the separate maximum-distance stopping
condition from Algorithm 2. This establishes correctness and finite termination;
the claimed cubic progress and sharper size bound are not assumed. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset DirectedPaths ChainUnion ChainFirst NormalizedReachability
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def algorithm (D : ℕ) (hD : 2 ≤ D) : FiniteThresholdGreedy.System (V × V) where
  candidates := candidates T.G
  potential := T.potential
  stopped := T.stopped D
  stopped_mono := T.stopped_mono D
  progress := fun H _ => T.progress D hD H

noncomputable def output (D : ℕ) (hD : 2 ≤ D) : Finset (V × V) :=
  ((T.algorithm D hD).run (candidates T.G).card).1

theorem output_legal (D : ℕ) (hD : 2 ≤ D) : T.output D hD ⊆ candidates T.G :=
  ((T.algorithm D hD).run (candidates T.G).card).2

theorem output_card (D : ℕ) (hD : 2 ≤ D) :
    (T.output D hD).card ≤ Fintype.card V ^ 2 := by
  calc
    (T.output D hD).card ≤ (candidates T.G).card := Finset.card_le_card (T.output_legal D hD)
    _ ≤ Fintype.card (V × V) := Finset.card_le_univ _
    _ = Fintype.card V ^ 2 := by simp [pow_two]

theorem output_stopped (D : ℕ) (hD : 2 ≤ D) : T.stopped D (T.output D hD) :=
  (T.algorithm D hD).run_terminates

/-- The selected greedy output has actual normalized walks of cost at most D
for every source/earliest-entry pair; reachability is never merely assumed. -/
theorem output_correct (D : ℕ) (hD : 2 ≤ D) {s t : V} (hst : (s,t) ∈ T.important) :
    ∃ p : DWalk s t,Allowed (T.graph (T.output D hD) s) p ∧ T.count p ≤ D := by
  obtain ⟨p,hp,he⟩ := T.distance_spec (T.output D hD) (T.important_spec hst).1
  exact ⟨p,hp,he.le.trans (T.output_stopped D hD (s,t) hst)⟩

/-- The full Algorithm 2 shortcut set includes the constructed preprocessing
union as well as the edges selected by the raw-sum greedy stage. -/
noncomputable def shortcuts (D : ℕ) (hD : 2 ≤ D) : Finset (V × V) :=
  T.base ∪ T.output D hD

theorem shortcuts_legal (D : ℕ) (hD : 2 ≤ D) : T.shortcuts D hD ⊆ candidates T.G :=
  Finset.union_subset (ChainNormalization.union_subset T.chains T.witnesses) (T.output_legal D hD)

theorem shortcuts_card (D : ℕ) (hD : 2 ≤ D) :
    (T.shortcuts D hD).card ≤ T.K * Fintype.card V + Fintype.card V ^ 2 := by
  exact Finset.card_union_le _ _ |>.trans (Nat.add_le_add
    (ChainNormalization.union_card_le T.chains T.disjoint T.witnesses) (T.output_card D hD))

theorem shortcuts_reachable_iff (D : ℕ) (hD : 2 ≤ D) (s t : V) :
    Reachable (augment T.G (T.shortcuts D hD)) s t ↔ Reachable T.G s t :=
  reachable_augment_iff T.G _ (T.shortcuts_legal D hD) s t

end GreedyShortcuts.ChainDistance.Context
