import LengthExpander.FiniteTermination
import LengthExpander.SequentialDemandGeometry
import LengthExpander.ForestPartition

/-! Instantiate the repaired matching construction from an actual sparse
cut sequence. Witness demands are chosen at their attained finite maximum;
sequential metric geometry is proved from the cuts, not assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- The original metric after the first i cuts (constant past the end). -/
def sequenceWeight (w : EdgeLength V) (scale : ℝ) : List (EdgeLength V) → ℕ → EdgeLength V
  | _, 0 => w
  | [], _+1 => w
  | C :: Cs, i+1 => sequenceWeight (applyCut w C scale) scale Cs i

@[simp] theorem sequenceWeight_zero (w : EdgeLength V) (scale : ℝ) (Cs) :
    sequenceWeight w scale Cs 0 = w := by cases Cs <;> rfl

@[simp] theorem sequenceWeight_nil (w : EdgeLength V) (scale : ℝ) (i) :
    sequenceWeight w scale [] i = w := by cases i <;> rfl

@[simp] theorem sequenceWeight_cons (w C : EdgeLength V) (scale : ℝ) (Cs) (i) :
    sequenceWeight w scale (C::Cs) (i+1) =
      sequenceWeight (applyCut w C scale) scale Cs i := rfl

theorem sequenceWeight_eq_prefix (w : EdgeLength V) (scale : ℝ) (Cs) (i) :
    sequenceWeight w scale Cs i = applyCut w (totalCut (Cs.take i)) scale := by
  induction Cs generalizing w i with
  | nil => simp
  | cons C Cs ih =>
    cases i with
    | zero => simp
    | succ i => simpa only [sequenceWeight_cons,List.take_succ_cons,totalCut_cons,applyCut_add]
        using ih (applyCut w C scale) i

theorem sequenceWeight_step (w : EdgeLength V) (scale : ℝ) (Cs)
    (i : Fin Cs.length) :
    sequenceWeight w scale Cs (i.val+1) =
      applyCut (sequenceWeight w scale Cs i.val) Cs[i.val] scale := by
  induction Cs generalizing w with
  | nil => exact Fin.elim0 i
  | cons C Cs ih =>
    rcases i with ⟨i,hi⟩
    cases i with
    | zero => simp
    | succ i =>
      simpa only [sequenceWeight_cons,List.getElem_cons_succ] using
        ih (applyCut w C scale) ⟨i,by simpa using hi⟩

variable {G : SimpleGraph V} {U : Sym2 V → ℕ} {A : NodeWeight V}
    {w : EdgeLength V} {h s φ : ℝ} {Cs : List (EdgeLength V)}

theorem sparseSequence_at (hCs : SparseSequence G U A h s φ w Cs)
    (i : Fin Cs.length) :
    SparseCut G U (sequenceWeight w (h*s) Cs i.val) A h s φ Cs[i.val] := by
  induction Cs generalizing w with
  | nil => exact Fin.elim0 i
  | cons C Cs ih =>
    rcases i with ⟨i,hi⟩
    cases i with
    | zero => exact hCs.1
    | succ i =>
      simpa only [sequenceWeight_cons,List.getElem_cons_succ] using
        ih hCs.2 ⟨i,by simpa using hi⟩

theorem sequenceWeight_mono (hCs : SparseSequence G U A h s φ w Cs)
    (hscale : 0 ≤ h*s) :
    ∀ i j, i ≤ j → ∀ e, sequenceWeight w (h*s) Cs i e ≤ sequenceWeight w (h*s) Cs j e := by
  have step : ∀ i e, sequenceWeight w (h*s) Cs i e ≤ sequenceWeight w (h*s) Cs (i+1) e := by
    induction Cs generalizing w with
    | nil => simp
    | cons C Cs ih =>
      intro i e
      cases i with
      | zero => simpa using le_applyCut w C hscale hCs.1.1 e
      | succ i => exact ih hCs.2 i e
  intro i j hij e
  exact (monotone_nat_of_le_succ (fun i => step i e)) hij

/-- Every sparse-cut sequence constructs its maximum witness demands and
all geometry needed for the repaired Appendix A matching graph. -/
theorem sparseSequence_witness_geometry {s : ℕ}
    (hCs : SparseSequence G U A h (s:ℝ) φ w Cs) (hh : 0 ≤ h) :
    ∃ D : Fin Cs.length → Demand V,
      (∀ i, Respects (D i) A) ∧
      (∀ i, demandSize (D i) = demandVolume G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s) ∧
      SequentialDemandGeometry G (sequenceWeight w (h*s) Cs) h s D := by
  classical
  let D (i : Fin Cs.length) := (exists_volume_witness G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s).choose
  have hD (i : Fin Cs.length) := (exists_volume_witness G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s).choose_spec
  refine ⟨D,fun i => (hD i).1.1,fun i => (hD i).2,?_⟩
  refine ⟨sequenceWeight_mono hCs (mul_nonneg hh (Nat.cast_nonneg s)),?_,?_⟩
  · intro i u v hp
    exact (hD i).1.2.1 u v hp
  · intro i u v hp
    rw [sequenceWeight_step]
    exact (hD i).1.2.2 u v hp

/-- The actual finite auxiliary graph of a sparse-cut sequence has the
repaired vertex count, exact total demand-volume edge count, and a genuine
parallel-greedy forest partition. -/
theorem sparseSequence_matching_forest {s : ℕ}
    (hCs : SparseSequence G U A h (s:ℝ) φ w Cs) (hh : 0 ≤ h) (hs : 2 ≤ s) :
    ∃ (H : SimpleGraph (DirectedCopies A)) (index : Sym2 (DirectedCopies A) → ℕ),
      IsParallelGreedy H index s ∧
      Fintype.card H.edgeSet = ∑ i : Fin Cs.length,
        demandVolume G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s ∧
      ∃ P : Fin (densityBudget (2*weightSize A) s) → SimpleGraph (DirectedCopies A),
        (∀ i, (P i).IsAcyclic) ∧ (∀ i, P i ≤ H) ∧
        (∀ u v, H.Adj u v → ∃! i, (P i).Adj u v) := by
  classical
  obtain ⟨D,hr,hsize,hgeo⟩ := sparseSequence_witness_geometry hCs hh
  let a i := demandAllocation (hr i)
  have hpg := hgeo.parallelGreedy a hh (by omega)
  refine ⟨familyGraph a,reverseIndex a,hpg,?_,?_⟩
  · rw [familyGraph_edge_card a (hgeo.supportDisjoint hh (by omega))]
    exact sum_congr rfl (fun i _ => hsize i)
  · have hf := @parallelGreedy_forest_partition (DirectedCopies A) inferInstance
      (familyGraph a) (reverseIndex a) s hpg hs
    exact (card_directedCopies A) ▸ hf


end LengthExpander
