import GreedyShortcuts.FiniteGreedy
import GreedyShortcuts.FiniteCharging
import Mathlib.Data.Nat.Log

/-! A constructed finite greedy hitting set. Its size follows from actual
incidence counting; no probabilistic existence axiom is used. -/
namespace GreedyShortcuts.FiniteHitting
open Finset
variable {V D : Type*} [Fintype V] [DecidableEq V] [DecidableEq D]

noncomputable def missed (F : D → Finset V) (d : D) (S : Finset V) : ℕ := by
  classical
  exact if Disjoint (F d) S then 1 else 0

noncomputable def potential (Q : Finset D) (F : D → Finset V) (S : Finset V) : ℕ :=
  ∑ d ∈ Q,missed F d S

omit [Fintype V] [DecidableEq D] in
theorem missed_mono (F : D → Finset V) (d : D) {S T : Finset V} (hST : S ⊆ T) :
    missed F d T ≤ missed F d S := by
  classical
  unfold missed
  split_ifs with ht hs
  · omega
  · exact False.elim (hs (ht.mono_right hST))
  · omega
  · omega

omit [Fintype V] [DecidableEq D] in
theorem missed_hit (F : D → Finset V) {d : D} {v : V} (hv : v ∈ F d) (S : Finset V) :
    missed F d (insert v S) = 0 := by
  classical
  simp only [missed,ite_eq_right_iff]
  intro hd
  exact False.elim ((Finset.disjoint_left.mp hd) hv (Finset.mem_insert_self _ _))

theorem averaged_progress (Q : Finset D) (F : D → Finset V) (r : ℕ)
    (hr : 0<r) (hF : ∀ d ∈ Q,r ≤ (F d).card) (S : Finset V)
    (hpos : 0 < potential Q F S) :
    ∃ v : V,r*potential Q F S ≤ Fintype.card V*(potential Q F S-potential Q F (insert v S)) := by
  classical
  have hQ : ∃ d ∈ Q,0 < missed F d S := by
    simpa only [potential,Finset.sum_pos_iff] using hpos
  obtain ⟨d,hd,_⟩ := hQ
  have hn : (F d).Nonempty := Finset.card_pos.mp (hr.trans_le (hF d hd))
  have hu : (Finset.univ : Finset V).Nonempty := hn.mono (Finset.subset_univ _)
  obtain ⟨v,hv,hvdrop⟩ := FiniteCharging.exists_large_drop Finset.univ Q hu
    (fun d => missed F d S) (fun v d => missed F d (insert v S)) r
    (fun v _ d _ => missed_mono F d (Finset.subset_insert v S)) (by
      intro d hd
      exact (Nat.mul_le_mul_right (missed F d S) (hF d hd)).trans
        (FiniteCharging.repair_charge Finset.univ (F d) (Finset.subset_univ _)
          (missed F d S) (fun v => missed F d (insert v S))
          (fun v hv => missed_hit F hv S)))
  exact ⟨v,by simpa only [Finset.card_univ,potential] using hvdrop⟩

noncomputable def system (Q : Finset D) (F : D → Finset V) (r : ℕ)
    (hr : 0<r) (hF : ∀ d ∈ Q,r ≤ (F d).card) : FiniteGreedy.System V where
  candidates := Finset.univ
  potential := potential Q F
  progress := by
    intro S hS hp
    obtain ⟨v,hv⟩ := averaged_progress Q F r hr hF S hp
    refine ⟨v,Finset.mem_univ _,?_⟩
    by_contra hnot
    have hz : potential Q F S-potential Q F (insert v S)=0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz,Nat.mul_zero] at hv
    nlinarith

noncomputable def output (Q : Finset D) (F : D → Finset V) (r : ℕ)
    (hr : 0<r) (hF : ∀ d ∈ Q,r ≤ (F d).card) : Finset V :=
  ((system Q F r hr hF).run (Fintype.card V)).1

theorem output_hits (Q : Finset D) (F : D → Finset V) (r : ℕ)
    (hr : 0<r) (hF : ∀ d ∈ Q,r ≤ (F d).card) {d : D} (hd : d ∈ Q) :
    ∃ v ∈ F d,v ∈ output Q F r hr hF := by
  classical
  have hz := (system Q F r hr hF).run_terminates
  change potential Q F (output Q F r hr hF) = 0 at hz
  have hm : missed F d (output Q F r hr hF) = 0 :=
    (Finset.sum_eq_zero_iff.mp hz) d hd
  have hn : ¬ Disjoint (F d) (output Q F r hr hF) := by
    intro hh
    simp [missed,hh] at hm
  exact Finset.not_disjoint_iff.mp hn

theorem output_card (Q : Finset D) (F : D → Finset V) (r : ℕ)
    (hr : 0<r) (hF : ∀ d ∈ Q,r ≤ (F d).card) :
    (output Q F r hr hF).card ≤ (Nat.log 2 Q.card+1)*(Fintype.card V/r+1) := by
  classical
  apply (system Q F r hr hF).final_card_of_relative_progress (Fintype.card V/r+1)
    (Nat.log 2 Q.card+1) (Nat.zero_lt_succ _)
  · intro S hp
    obtain ⟨v,hv⟩ := averaged_progress Q F r hr hF S.1 hp
    exact ⟨v,Finset.mem_univ _,FiniteCharging.relative_progress _ _ _ _ hr hv⟩
  · have he : potential Q F ∅ = Q.card := by simp [potential,missed]
    change potential Q F ∅ < _
    rw [he]
    exact Nat.lt_pow_succ_log_self (by decide) _

end GreedyShortcuts.FiniteHitting
