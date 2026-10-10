import LengthExpander.Cuts
import LengthExpander.SourceCorrections

/-! A graph-level counterexample to monotonicity of length-constrained
expansion under further length increases. This justifies keeping the
maximality conclusion at the unscaled output. -/
namespace LengthExpander.SourceCorrections
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

private theorem bool_edgeFinset : (⊤ : SimpleGraph Bool).edgeFinset = {s(false,true)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => cases u <;> cases v <;> simp [Sym2.eq_iff]

private theorem bool_cutCost (C : EdgeLength Bool) :
    cutCost (⊤ : SimpleGraph Bool) (fun _ => 100) C = 100*C s(false,true) := by
  classical
  unfold cutCost
  apply Finset.sum_eq_single s(false,true)
  · intro e he hne
    exfalso
    apply hne
    induction e using Sym2.inductionOn with
    | _ u v => cases u <;> cases v <;> simp_all [Sym2.eq_iff]
  · intro he
    exact False.elim (he (by simp))

private theorem constant_near {a b : ℝ} (ha : a ≤ b) (hb : 0 ≤ b) (u v : Bool) :
    Near (⊤ : SimpleGraph Bool) (fun _ => a) b u v := by
  by_cases h : u = v
  · subst v; exact ⟨.nil,by simpa using hb⟩
  · exact ⟨.cons (by simpa using h) .nil,by simpa using ha⟩

private theorem constant_walk_nonneg {a : ℝ} (ha : 0 ≤ a) {u v : Bool}
    (p : (⊤ : SimpleGraph Bool).Walk u v) : 0 ≤ walkLength (fun _ => a) p := by
  induction p with
  | nil => simp
  | cons huv p ih => simpa using add_nonneg ha ih

private theorem constant_far {a b : ℝ} (ha : 0 ≤ a) (hab : b < a)
    {u v : Bool} (huv : u ≠ v) : Far (⊤ : SimpleGraph Bool) (fun _ => a) b u v := by
  intro p
  cases p with
  | nil => exact False.elim (huv rfl)
  | cons h p => simpa using lt_of_lt_of_le hab (le_add_of_nonneg_right (constant_walk_nonneg ha p))

private theorem volume_zero_of_all_near {w C : EdgeLength Bool} {h s : ℝ}
    (hall : ∀ u v, Near (⊤ : SimpleGraph Bool) (applyCut w C (h*s)) (h*s) u v) :
    demandVolume ⊤ w C unitWeight h s = 0 := by
  obtain ⟨D,hD,hsize⟩ := exists_volume_witness (⊤ : SimpleGraph Bool) w C unitWeight h s
  have hz : ∀ u v, D u v = 0 := by
    intro u v
    by_contra hn
    exact (far_iff_not_near.mp (hD.2.2 u v (Nat.pos_of_ne_zero hn))) (hall u v)
  rw [← hsize]
  simp [demandSize,hz]

/-- The one-edge graph at length 2/5 is a (1,2)-length 35-expander
with edge capacity 100 and unit node budgets. -/
theorem short_edge_expands :
    IsExpander (⊤ : SimpleGraph Bool) (fun _ => 100) (fun _ => 2/5)
      unitWeight 1 2 35 := by
  intro C hC
  have hc := sparseCut_size_bound (by norm_num : (0:ℝ) ≤ 35) hC
  rw [bool_cutCost] at hc
  norm_num [weightSize,unitWeight,Fintype.sum_bool] at hc
  have hCe : C s(false,true) ≤ 7/10 := by linarith
  have hall : ∀ u v, Near (⊤ : SimpleGraph Bool)
      (applyCut (fun _ => 2/5) C (1*2)) (1*2) u v := by
    intro u v
    by_cases he : u = v
    · subst v; exact ⟨.nil,by norm_num⟩
    · have hcuv : C s(u,v) = C s(false,true) := by
        cases u <;> cases v <;> simp_all [Sym2.eq_swap]
      refine ⟨.cons (by simpa using he) .nil,?_⟩
      simp only [walkLength_cons,walkLength_nil,add_zero,applyCut,hcuv]
      linarith
  have hz := volume_zero_of_all_near hall
  exact (Nat.ne_of_gt hC.2.1) hz

/-- Doubling that edge length to 4/5 creates a sparse cut: adding 13/20
at scale two costs 65, separates two directed units, and gives length 21/10. -/
theorem doubled_edge_not_expander :
    ¬ IsExpander (⊤ : SimpleGraph Bool) (fun _ => 100) (fun _ => 4/5)
      unitWeight 1 2 35 := by
  intro hExp
  apply hExp (fun _ => 13/20)
  have hw : CutWitness (⊤ : SimpleGraph Bool) (fun _ => 4/5) (fun _ => 13/20)
      unitWeight 1 2 twoWay := by
    refine ⟨twoWay_respects,?_,?_⟩
    · intro u v _; exact constant_near (by norm_num) (by norm_num) u v
    · intro u v hp
      have huv : u ≠ v := by intro he; simp [twoWay,he] at hp
      have heq : applyCut (fun _ : Sym2 Bool => (4/5:ℝ)) (fun _ => 13/20) (1*2) = (fun _ => (21/10:ℝ)) := by
        funext e; norm_num [applyCut]
      rw [heq]
      exact constant_far (by norm_num) (by norm_num) huv
  have hv : 2 ≤ demandVolume (⊤ : SimpleGraph Bool) (fun _ => 4/5) (fun _ => 13/20)
      unitWeight 1 2 := by simpa only [twoWay_size] using witness_size_le_volume hw
  refine ⟨by intro e; norm_num,by omega,?_⟩
  rw [bool_cutCost]
  have hv' : (2:ℝ) ≤ demandVolume (⊤ : SimpleGraph Bool) (fun _ => 4/5) (fun _ => 13/20)
      unitWeight 1 2 := by exact_mod_cast hv
  linarith

/-- Expansion is not monotone under nonnegative length increases. -/
theorem expansion_not_monotone_under_length_increase :
    ∃ w w' : EdgeLength Bool, (∀ e, 0 ≤ w e ∧ w e ≤ w' e) ∧
      IsExpander (⊤ : SimpleGraph Bool) (fun _ => 100) w unitWeight 1 2 35 ∧
      ¬ IsExpander (⊤ : SimpleGraph Bool) (fun _ => 100) w' unitWeight 1 2 35 := by
  exact ⟨fun _ => 2/5,fun _ => 4/5,by intro e; norm_num,
    short_edge_expands,doubled_edge_not_expander⟩

end LengthExpander.SourceCorrections
