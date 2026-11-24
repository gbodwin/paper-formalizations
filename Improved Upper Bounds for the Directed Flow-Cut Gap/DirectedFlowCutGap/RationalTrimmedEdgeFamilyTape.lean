import DirectedFlowCutGap.RationalTrimmedEdgeFamily

/-! Draw from the guarded trimmed family with bounded rejection, retaining
the original graph and weight guarantees on the resulting literal tape. -/
namespace DirectedFlowCutGap.RationalTrimmedEdgeFamilyTape

open scoped NNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalExactEdgeOracle (Edge)
open RationalEdgeDecomposition (Good originalWeight)
open RationalTrimmedEdgeFamily (family family_nonempty family_spec)

variable {n : ℕ}

def draw (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape) :=
  EncodedSolverBits.run (BinaryFamilySampler.choose (family A w).cuts trials) tape

theorem draw_used (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool)
    (enough : trials*FairBitWords.width (family A w).cuts.length ≤ tape.length) :
    ∃ cut paid used, draw A w trials tape = some ((cut,paid),(tape.drop used,used)) ∧
      used ≤ trials*FairBitWords.width (family A w).cuts.length :=
  BinaryFamilySampler.choose_used _ _ _ enough

theorem draw_valid (hn : 0 < n) (A : Adjacency n) (w : Weights n) {trials : ℕ} {tape rest : List Bool}
    {cut : Finset (Edge n)} {paid used : ℕ}
    (played : draw A w trials tape = some ((some cut,paid),(rest,used))) : Good A w cut := by
  let familyCuts := (family A w).cuts
  have seen := EncodedSolverBits.run_support (BinaryFamilySampler.choose_binary familyCuts trials) played
  have inList := (BinaryFamilySampler.choose_supported familyCuts trials seen).1 cut (by simp)
  exact (family_spec hn A w).1 cut inList

theorem draw_law (hn : 0 < n) (A : Adjacency n) (w : Weights n) (trials : ℕ) :
    let cuts := (family A w).cuts
    let q := trials*FairBitWords.width cuts.length
    let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
    p none = BoundedBitRejection.law cuts.length trials none ∧
      ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤
        8*(originalWeight A w e : ℝ)*(ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  let cuts := (family A w).cuts
  let q := trials*FairBitWords.width cuts.length
  let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
  change p none = _ ∧ ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤ _
  have eq : p = (FiniteDrawTrees.ideal (BinaryFamilySampler.choose cuts trials)).map Prod.fst := by
    have law := congrArg (PMF.map (fun o : Option (Option (Finset (Edge n)) × ℕ) => (o.map Prod.fst).join))
      (EncodedSolverBits.run_fairTape (BinaryFamilySampler.choose_within cuts trials)
        (BinaryFamilySampler.choose_binary cuts trials))
    simpa only [p,q,PMF.map_comp,Function.comp_def,Option.map_map,Option.map_some,Option.join_some,draw] using law
  rw [eq]
  refine ⟨BinaryFamilySampler.choose_failure cuts (family_nonempty A w) trials,fun e => ?_⟩
  rw [BinaryFamilySampler.choose_marginal cuts (family_nonempty A w) trials (fun X => e ∈ X)]
  have nonnegative : (0 : ℝ) ≤ (cuts.countP (fun X => decide (e ∈ X)) : ℝ)/(cuts.length : ℝ) := by positivity
  exact (mul_le_of_le_one_left nonnegative (sub_le_self _ ENNReal.toReal_nonneg)).trans ((family_spec hn A w).2 e)

end DirectedFlowCutGap.RationalTrimmedEdgeFamilyTape
