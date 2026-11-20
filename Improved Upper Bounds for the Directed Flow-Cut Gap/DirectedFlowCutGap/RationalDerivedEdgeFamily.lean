import DirectedFlowCutGap.RationalInstanceEdgeFactor
import DirectedFlowCutGap.RationalOriginalEdgeFamily

/-! The original rational uniform family and tape sampler can derive an
instance factor from the input, with loss bounded by the original-total
parameter. The search for the factor and the cut oracle are exhaustive. -/
namespace DirectedFlowCutGap.RationalDerivedEdgeFamily

open scoped NNRat NNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalEdgeDecomposition (Good originalWeight)
open RationalExactEdgeOracle (Edge)

def factor {n : ℕ} (A : Adjacency n) (w : Weights n) : ℚ≥0 :=
  (RationalInstanceEdgeFactor.least A w : ℚ≥0)

theorem factor_valid {n : ℕ} (A : Adjacency n) (w : Weights n) :
    HasEdgeRoundingFactor (graph A) (weights w) (factor A w : ℝ) := by
  simpa only [factor,NNRat.cast_natCast] using RationalInstanceEdgeFactor.least_valid A w

private theorem loss_le {n : ℕ} (A : Adjacency n) (w : Weights n) (e : Edge n) :
    8*(originalWeight A w e : ℝ)*(factor A w : ℝ) ≤
      8*(originalWeight A w e : ℝ)*
        (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  simp only [factor,NNRat.cast_natCast]
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (RationalInstanceEdgeFactor.least_le_original_factor A w))
    (mul_nonneg (by norm_num) (NNRat.cast_nonneg _))

def family {n : ℕ} (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  RationalOriginalEdgeFamily.adaptive A w (factor A w)

theorem family_spec {n : ℕ} (A : Adjacency n) (w : Weights n) :
    let L := (family A w).cuts
    0<L.length ∧ (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  refine ⟨RationalOriginalEdgeFamily.adaptive_nonempty A w _,?_⟩
  by_cases hn : 0<n
  · have spec := RationalOriginalEdgeFamily.adaptive_spec_all hn A w _ (factor_valid A w)
    exact ⟨spec.1,fun e => (spec.2 e).trans (loss_le A w e)⟩
  · have h : n=0 := by omega
    subst n
    exact ⟨fun X _ => ⟨fun e _ => Fin.elim0 e.1,fun s => Fin.elim0 s⟩,fun e => Fin.elim0 e.1⟩

noncomputable def law {n : ℕ} (A : Adjacency n) (w : Weights n) : PMF (Finset (Edge n)) :=
  RationalOriginalEdgeFamily.law A w (factor A w)

theorem law_spec {n : ℕ} (A : Adjacency n) (w : Weights n) :
    (∀ X ∈ (law A w).support, Good A w X) ∧
      ∀ e, ((law A w).toOuterMeasure {X | e ∈ X}).toReal ≤
        8*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  by_cases hn : 0<n
  · have spec := RationalOriginalEdgeFamily.law_spec hn A w _ (factor_valid A w)
    exact ⟨spec.1,fun e => (spec.2 e).trans (loss_le A w e)⟩
  · have h : n=0 := by omega
    subst n
    exact ⟨fun X _ => ⟨fun e _ => Fin.elim0 e.1,fun s => Fin.elim0 s⟩,fun e => Fin.elim0 e.1⟩

def draw {n : ℕ} (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape) :=
  RationalOriginalEdgeFamily.draw A w (factor A w) trials tape

theorem draw_used {n : ℕ} (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool)
    (enough : trials*FairBitWords.width (family A w).cuts.length ≤ tape.length) :
    ∃ cut paid used, draw A w trials tape=some ((cut,paid),(tape.drop used,used)) ∧
      used ≤ trials*FairBitWords.width (family A w).cuts.length :=
  RationalOriginalEdgeFamily.draw_used A w _ trials tape enough

theorem draw_valid {n : ℕ} (A : Adjacency n) (w : Weights n) {trials : ℕ}
    {tape rest : List Bool} {cut : Finset (Edge n)} {paid used : ℕ}
    (found : draw A w trials tape=some ((some cut,paid),(rest,used))) : Good A w cut := by
  by_cases hn : 0<n
  · exact RationalOriginalEdgeFamily.draw_valid hn A w _ (factor_valid A w) found
  · have h : n=0 := by omega
    subst n
    exact ⟨fun e _ => Fin.elim0 e.1,fun s => Fin.elim0 s⟩

theorem draw_law {n : ℕ} (hn : 0<n) (A : Adjacency n) (w : Weights n) (trials : ℕ) :
    let L := (family A w).cuts
    let q := trials*FairBitWords.width L.length
    let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
    p none = BoundedBitRejection.law L.length trials none ∧
      ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤
        8*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  have spec := RationalOriginalEdgeFamily.draw_law hn A w _ (factor_valid A w) trials
  exact ⟨spec.1,fun e => (spec.2 e).trans (loss_le A w e)⟩

end DirectedFlowCutGap.RationalDerivedEdgeFamily
