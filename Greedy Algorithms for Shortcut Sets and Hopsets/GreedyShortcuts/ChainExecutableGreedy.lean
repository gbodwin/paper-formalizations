import GreedyShortcuts.FiniteExecutableGreedy
import GreedyShortcuts.ChainExecutableObjective
import GreedyShortcuts.ChainHopCorrectness

/-! A deterministic executable raw-greedy stage for supplied chain data.
It obeys the same objective and stopping test, with an explicit list-order tie
rule. Equality with the old unspecified Classical.choice output is not claimed. -/
namespace GreedyShortcuts.ChainExecutableGreedy
open Finset DirectedPaths ChainExecutableObjective FiniteExecutableGreedy
open LinearDistancePreservers.ConsistentTiebreaking
variable {n m : ℕ}

def choices (edge : Fin n → Fin n → Bool) : List (Fin n×Fin n) :=
  ((List.finRange n).flatMap (fun s => (List.finRange n).map (fun t => (s,t)))).filter
    (fun st => decide (st.1≠st.2) && FiniteReachabilityDP.reaches edge st.1 st.2)

theorem choices_iff (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (e : Fin n×Fin n) : e∈choices edge ↔ e∈DirectedPaths.candidates T.G := by
  rcases e with ⟨s,t⟩
  simp [choices,DirectedPaths.mem_candidates,FiniteReachabilityDP.reaches_iff T.G T.acyclic edge he]

def output (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (D : ℕ) : Finset (Fin n×Fin n) :=
  run (choices edge) (potential T edge) (stopped T edge D) (choices edge).toFinset.card

theorem represents (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (hD : 2≤D) :
    Represents (T.algorithm D hD) (choices edge) (potential T edge) (stopped T edge D) where
  choices_iff := choices_iff T edge he
  score_eq := fun H hH => potential_eq T edge he H hH
  stopped_iff := fun H hH => stopped_iff T edge he D H hH

theorem output_legal (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (hD : 2≤D) : output T edge D⊆DirectedPaths.candidates T.G :=
  (represents T edge he D hD).run_legal _

theorem output_stopped (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (hD : 2≤D) : T.stopped D (output T edge D) :=
  (represents T edge he D hD).run_terminates

theorem active_step_minimizes (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (hD : 2≤D) (H : Finset (Fin n×Fin n))
    (hH : H⊆DirectedPaths.candidates T.G) (hs : ¬T.stopped D H) :
    ∃e∈DirectedPaths.candidates T.G,
      step (choices edge) (potential T edge) (stopped T edge D) H=insert e H ∧
      ∀f∈DirectedPaths.candidates T.G,T.potential (insert e H)≤T.potential (insert f H) :=
  (represents T edge he D hD).step_minimizes H hH hs

theorem output_card (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (hD : 2≤D) : (output T edge D).card≤n^2 := by
  exact (Finset.card_le_card (output_legal T edge he D hD)).trans
    (by simpa [pow_two] using Finset.card_le_univ (DirectedPaths.candidates T.G))

/-- Actual output hop correctness, including the separately retained base. -/
theorem output_hop_bound (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (hD : 2≤D) {U : ℕ} (hcover : ChainCover.IsCover T U)
    {s t : Fin n} (hr : Reachable T.G s t) :
    ∃q : DWalk s t,Allowed (augment T.G (T.base∪output T edge D)) q ∧
      q.length≤2*U+5*D+4 :=
  T.stopped_hop_bound hcover (output_legal T edge he D hD) (output_stopped T edge he D hD) hr

end GreedyShortcuts.ChainExecutableGreedy
