import LengthExpander.Cuts
import Lean.Elab.Tactic.Omega

/-! Finite termination for the maximal sparse-cut sequence in Theorem 5.1.
No compactness, infinite sum, minimum positive length increase or termination
oracle is assumed: every chosen cut removes a currently near ordered pair. -/
namespace LengthExpander
open Finset SimpleGraph
variable {V : Type*} [Fintype V]

noncomputable def nearPairs (G : SimpleGraph V) (w : EdgeLength V) (h : ℝ) :
    Finset (V × V) := by
  classical
  exact univ.filter (fun x => Near G w h x.1 x.2)

@[simp] theorem mem_nearPairs {G : SimpleGraph V} {w : EdgeLength V}
    {h : ℝ} {u v : V} : (u,v) ∈ nearPairs G w h ↔ Near G w h u v := by
  classical
  simp [nearPairs]

theorem nearPairs_mono {G : SimpleGraph V} {w w' : EdgeLength V}
    (hw : ∀ e, w e ≤ w' e) (h : ℝ) : nearPairs G w' h ⊆ nearPairs G w h := by
  intro x hx
  exact mem_nearPairs.mpr (near_length_mono hw (mem_nearPairs.mp hx))

theorem positive_demand_has_pair {D : Demand V} (hD : 0 < demandSize D) :
    ∃ u v, 0 < D u v := by
  classical
  by_contra hex
  have hz : ∀ u v, D u v = 0 := by
    intro u v
    by_contra hn
    exact hex ⟨u,v,Nat.pos_of_ne_zero hn⟩
  simp [demandSize, hz] at hD

theorem sparseCut_decreases_nearPairs {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {w C : EdgeLength V} {A : NodeWeight V} {h s φ : ℝ}
    (hh : 0 ≤ h) (hs : 1 ≤ s) (hC : SparseCut G U w A h s φ C) :
    (nearPairs G (applyCut w C (h*s)) h).card < (nearPairs G w h).card := by
  classical
  have hhs : 0 ≤ h*s := mul_nonneg hh (le_trans (by norm_num) hs)
  have hsub := nearPairs_mono (G := G) (le_applyCut w C hhs hC.1) h
  obtain ⟨D,hD,hsize⟩ := exists_volume_witness G w C A h s
  obtain ⟨u,v,huv⟩ := positive_demand_has_pair (by rw [hsize]; exact hC.2.1)
  have hbefore : (u,v) ∈ nearPairs G w h := mem_nearPairs.mpr (hD.2.1 u v huv)
  have hafter : (u,v) ∉ nearPairs G (applyCut w C (h*s)) h := by
    intro hmem
    obtain ⟨p,hp⟩ := mem_nearPairs.mp hmem
    have hfar := hD.2.2 u v huv p
    nlinarith
  apply card_lt_card
  exact (ssubset_iff_subset_ne).mpr ⟨hsub, fun heq => hafter (heq.symm ▸ hbefore)⟩

/-- A finite list of cuts sparse in the graph after its predecessors. -/
def SparseSequence (G : SimpleGraph V) (U : Sym2 V → ℕ) (A : NodeWeight V)
    (h s φ : ℝ) : EdgeLength V → List (EdgeLength V) → Prop
  | _, [] => True
  | w, C :: Cs => SparseCut G U w A h s φ C ∧
      SparseSequence G U A h s φ (applyCut w C (h*s)) Cs

def totalCut : List (EdgeLength V) → EdgeLength V
  | [] => fun _ => 0
  | C :: Cs => fun e => C e + totalCut Cs e

@[simp] theorem totalCut_nil : totalCut ([] : List (EdgeLength V)) = fun _ => 0 := rfl

@[simp] theorem totalCut_cons (C : EdgeLength V) (Cs : List (EdgeLength V)) :
    totalCut (C :: Cs) = fun e => C e + totalCut Cs e := rfl

theorem sequence_total_nonneg {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h s φ : ℝ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h s φ w Cs) : ∀ e, 0 ≤ totalCut Cs e := by
  induction Cs generalizing w with
  | nil => intro e; rfl
  | cons C Cs ih =>
    intro e
    exact add_nonneg (hCs.1.1 e) (ih hCs.2 e)

/-- A maximal sparse-cut sequence exists and has at most one round for
each ordered pair initially within h. This closes the termination step
left implicit in the proof of Theorem 5.1. -/
theorem exists_finite_maximal_sequence (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (A : NodeWeight V) (h s φ : ℝ) (hh : 0 ≤ h) (hs : 1 ≤ s)
    (w : EdgeLength V) :
    ∃ Cs, SparseSequence G U A h s φ w Cs ∧
      IsExpander G U (applyCut w (totalCut Cs) (h*s)) A h s φ ∧
      Cs.length ≤ (nearPairs G w h).card := by
  classical
  suffices aux : ∀ n : ℕ, ∀ w : EdgeLength V, (nearPairs G w h).card = n →
      ∃ Cs, SparseSequence G U A h s φ w Cs ∧
        IsExpander G U (applyCut w (totalCut Cs) (h*s)) A h s φ ∧ Cs.length ≤ n by
    exact aux _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn
    by_cases he : IsExpander G U w A h s φ
    · refine ⟨[], trivial, ?_, by simp⟩
      simpa using he
    · have hex : ∃ C, SparseCut G U w A h s φ C := by
        by_contra hx
        apply he
        intro C hC
        exact hx ⟨C,hC⟩
      obtain ⟨C,hC⟩ := hex
      have hlt : (nearPairs G (applyCut w C (h*s)) h).card < n := by
        rw [← hn]
        exact sparseCut_decreases_nearPairs hh hs hC
      obtain ⟨Cs,hCs,hExp,hLen⟩ := ih _ hlt (applyCut w C (h*s)) rfl
      refine ⟨C :: Cs, ⟨hC,hCs⟩, ?_, ?_⟩
      · simpa only [totalCut_cons, applyCut_add] using hExp
      · simp only [List.length_cons]
        omega

end LengthExpander
