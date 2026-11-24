import DirectedFlowCutGap.NormalizedVertexLP
import DirectedFlowCutGap.RationalSparsestVertexFairTape
import DirectedFlowCutGap.ConcurrentEdgeBudgetSelection

/-! Round the computed exact vertex optimum, choosing the smaller size or
mass scale by rational comparison. -/
namespace DirectedFlowCutGap.NormalizedVertexLPRound

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalSparsestVertexDistances (weights distance)
open RationalSparsestVertexThreshold (choose actualDistance)
open RationalSparsestVertexRound (Result scaled tapeBudget drawBound)
open RationalSparsestVertexExpectation (expectedSparsity normalizedMass)
open ConcurrentEdgeBudgetSelection (score scale)
open NormalizedOptimalMode (sizeScale massScale)
open EncodedUnitCostReplication (selectedSet)
open RationalSparsestEdgeRound (demandSet)
open FiniteHarmonicThreshold (harmonicWeight)

variable {m n : ℕ}

def averageMass (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m) : ℚ≥0 :=
  (m : ℚ≥0) * (∑ v : Fin n, (BinaryRational.decode (w.get v)).value) /
    ∑ j : Fin m, (distance A w P[j.val]).getD 0

theorem averageMass_eq (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m) :
    (averageMass A w P : ℝ≥0) = normalizedMass A w P := by
  have read (j : Fin m) : (((distance A w P[j.val]).getD 0 : ℚ≥0) : ℝ≥0) = actualDistance A w P j := by
    cases reachable : distance A w P[j.val] with
    | some d => exact RationalSparsestVertexDistances.finite_value A w P[j.val] reachable
    | none =>
      have absent := (RationalSparsestVertexDistances.none_iff A w P[j.val]).mp reachable
      simp only [actualDistance,SparsestVertexBridge.demandDistance,absent,ENNReal.toNNReal_top,
        Option.getD_none,NNRat.cast_zero]
  simp only [averageMass,normalizedMass,NNRat.cast_div,NNRat.cast_mul,NNRat.cast_natCast,
    NNRat.cast_sum,read,totalWeight]
  rfl

def encodePrice (q : ℚ) : ℚ≥0 := ⟨max q 0,le_max_right _ _⟩

def pick (A : Adjacency n) (w : Row n) (q : ℚ) (P : Vector (Fin n × Fin n) m) :
    ChargedVertexModes.Mode :=
  let a := encodePrice q
  let mass := averageMass A w P
  if score n m a mass .mass ≤ score n m a mass .size then .mass else .size

theorem picked_le (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m) (q : ℚ)
    (price : (weightedCost (weights c) (weights w) : ℝ) = (q : ℝ)) (mode : ChargedVertexModes.Mode) :
    scale n m (weightedCost (weights c) (weights w)) (normalizedMass A w P) (pick A w q P) ≤
      scale n m (weightedCost (weights c) (weights w)) (normalizedMass A w P) mode := by
  let a := encodePrice q
  let mass := averageMass A w P
  have qNonneg : 0 ≤ q := by exact_mod_cast price ▸ (NNReal.coe_nonneg _)
  have cost : (a : ℝ≥0) = weightedCost (weights c) (weights w) := by
    apply NNReal.eq
    change ((max q 0 : ℚ) : ℝ) = _
    rw [max_eq_left qNonneg,price]
  rw [← cost,← averageMass_eq]
  apply (ConcurrentEdgeBudgetSelection.score_le_iff n m a a mass mass _ _).mp
  unfold pick
  dsimp only
  split
  · cases mode
    · exact le_rfl
    · assumption
  · cases mode
    · exact le_of_not_ge ‹_›
    · exact le_rfl

def run (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m) (T : ℕ) (bits : Bits) :
    Option (ℚ × Result n) :=
  (NormalizedVertexLP.minimize A c P.get m).bind fun (q,w) =>
    (RationalSparsestVertexRound.run A w c P (pick A w q P) T bits).map fun result => (q,result)

private theorem entry (P : Vector (Fin n × Fin n) m) (i : Fin m) : P.get i = P[i.val] := by
  cases i
  rfl

theorem positive_threshold (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2)) (d : Fin m)
    (normal : (m : ℝ≥0) ≤ ∑ j : Fin m, SparsestVertexBridge.demandDistance (graph A) (weights w) (P.get j)) :
    ∃ i τ, choose A w P = .threshold i τ := by
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  cases found : choose A w P with
  | unreachable i =>
    rw [found] at spec
    have path := reach i
    rw [entry P i] at path
    exact (((vertexDistance_eq_top_iff (graph A) (weights w) _ _).mp spec) path).elim
  | zero =>
    rw [found] at spec
    have zero (j : Fin m) : SparsestVertexBridge.demandDistance (graph A) (weights w) (P.get j) = 0 := by
      rw [entry P j]
      simpa only [SparsestVertexBridge.demandDistance,ENNReal.toNNReal_zero]
        using congrArg ENNReal.toNNReal (spec j)
    have mpos : (0 : ℝ≥0) < m := by exact_mod_cast (Nat.zero_le _).trans_lt d.isLt
    simp only [zero,Finset.sum_const_zero] at normal
    exact ((not_le_of_gt mpos) normal).elim
  | threshold i τ => exact ⟨i,τ,rfl⟩

theorem solution (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2) :
    ∃ q w i τ, NormalizedVertexLP.minimize A c P.get m = some (q,w) ∧ choose A w P = .threshold i τ := by
  have normal := VertexNormalizedPotentials.normalized_of_nonadjacent (graph A) P.get (m : ℝ≥0)
    d (reach d) different noArc
  have complete := NormalizedVertexLP.minimize_complete A c P.get (m : ℚ≥0) (fun _ => m) reach
    (by simpa only [NNRat.cast_natCast] using normal)
  obtain ⟨⟨q,w⟩,found⟩ := Option.isSome_iff_exists.mp complete
  have normalized := (NormalizedVertexLP.minimize_attained A c P.get (m : ℚ≥0) reach found).1
  obtain ⟨i,τ,threshold⟩ := positive_threshold A w P reach d
    (by simpa only [NNRat.cast_natCast] using normalized)
  exact ⟨q,w,i,τ,found,threshold⟩

theorem complete (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (T : ℕ) (bits : Bits) (enough : tapeBudget n T ≤ bits.length) :
    ∃ q mask used, run A c P T bits = some (q,.cut mask (bits.drop used)) ∧ used ≤ tapeBudget n T := by
  obtain ⟨q,w,i,τ,found,threshold⟩ := solution A c P reach d different noArc
  obtain ⟨mask,used,performed,within⟩ := RationalSparsestVertexRound.run_complete A w c P threshold (pick A w q P) T bits enough
  exact ⟨q,mask,used,by simp only [run,found,Option.bind_some,performed,Option.map_some],within⟩

theorem cut_valid (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m) (T : ℕ)
    {bits rest : Bits} {q : ℚ} {mask : RetainedGridState.Flags n} (ran : run A c P T bits = some (q,.cut mask rest)) :
    0 < (SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card := by
  obtain ⟨⟨r,w⟩,_,after⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨result,performed,same⟩ := Option.map_eq_some_iff.mp after
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  exact RationalSparsestVertexRound.run_cut A w c P _ T performed

noncomputable section
open FiniteAmplification (probability)

theorem ideal_bound : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ}
    (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    (_distinct : Function.Injective fun j : Fin m => P[j.val])
    (_normal : (m : ℝ≥0) ≤ ∑ j, actualDistance A w P j)
    {i : Fin m} {τ : ℚ≥0}, choose A w P = .threshold i τ →
    ∀ (mode : ChargedVertexModes.Mode),
      expectedSparsity (scaled A w c τ) (demandSet P) mode ≤ K*(n : ℝ)^ε*
        scale n m (weightedCost (weights c) (weights w)) (normalizedMass A w P) mode := by
  intro ε positive
  obtain ⟨Ks,Kspos,size⟩ := RationalSparsestVertexExpectation.size_uniform ε positive
  obtain ⟨Km,_,mass⟩ := RationalSparsestVertexExpectation.mass_uniform ε positive
  let K := max Ks Km
  have KsK : Ks ≤ K := le_max_left _ _
  have KmK : Km ≤ K := le_max_right _ _
  refine ⟨K,Kspos.trans_le KsK,?_⟩
  intro m n A w c P distinct normal i τ threshold mode
  let S : ℝ := ∑ j, (actualDistance A w P j : ℝ)
  let C : ℝ := weightedCost (weights c) (weights w)
  let M : ℝ := normalizedMass A w P
  let H : ℝ := harmonicWeight m
  have mpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le _).trans_lt i.isLt
  have sum : (m : ℝ) ≤ S := by
    simpa only [S,NNReal.coe_sum,NNReal.coe_natCast] using NNReal.coe_le_coe.mpr normal
  have ratio : C/S ≤ C/(m : ℝ) := div_le_div_of_nonneg_left (NNReal.coe_nonneg _) mpos sum
  cases mode with
  | size =>
    calc
      _ ≤ Ks*(n : ℝ)^(1/3+ε)*H*(C/S) := size A w c P distinct threshold
      _ ≤ K*(n : ℝ)^(1/3+ε)*H*(C/(m : ℝ)) := by gcongr
      _ = _ := by
        simp only [scale,sizeScale]
        rw [Real.rpow_add_of_nonneg (by positivity : (0 : ℝ) ≤ n)
          (by norm_num : 0 ≤ (1/3 : ℝ)) positive.le]
        unfold C H
        ring
  | mass =>
    calc
      _ ≤ Km*(n : ℝ)^ε*H^(3/2 : ℝ)*M^(1/2 : ℝ)*(C/S) := mass A w c P distinct threshold
      _ ≤ K*(n : ℝ)^ε*H^(3/2 : ℝ)*M^(1/2 : ℝ)*(C/(m : ℝ)) := by gcongr
      _ = _ := by simp only [scale,massScale]; unfold C H M; ring

theorem probability_bound : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ}
    (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (_distinct : Function.Injective fun j : Fin m => P[j.val])
    (_reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    {q : ℚ} {w : Row n}, NormalizedVertexLP.minimize A c P.get m = some (q,w) →
    ∀ {i : Fin m} {τ : ℚ≥0}, choose A w P = .threshold i τ →
    ∀ mode : ChargedVertexModes.Mode, ∀ T : ℕ,
      let B := K*(n : ℝ)^ε*scale n m (weightedCost (weights c) (weights w)) (normalizedMass A w P) mode
      0 < B →
      probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
        (fun bits => (run A c P T bits).bind fun (_,result) => RationalSparsestVertexFairTape.observe result))
        (RationalSparsestVertexFairTape.bad (scaled A w c τ) (demandSet P) (2*B)) ≤
          1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  intro ε epos
  obtain ⟨K,Kpos,bound⟩ := ideal_bound ε epos
  refine ⟨K,Kpos,?_⟩
  intro m n A c P distinct reach q w found i τ threshold mode T B Bpositive
  have optimum := NormalizedVertexLP.minimize_attained A c P.get (m : ℚ≥0) reach found
  have normal : (m : ℝ≥0) ≤ ∑ j, actualDistance A w P j := by
    simpa only [actualDistance,← entry,NNRat.cast_natCast] using optimum.1
  have expected : expectedSparsity (scaled A w c τ) (demandSet P) (pick A w q P) ≤ B :=
    (bound A w c P distinct normal threshold (pick A w q P)).trans
      (mul_le_mul_of_nonneg_left (picked_le A w c P q optimum.2.1 mode) (by positivity))
  have observed (bits : Bits) :
      (run A c P T bits).bind (fun (_,result) => RationalSparsestVertexFairTape.observe result) =
        (RationalSparsestVertexRound.run A w c P (pick A w q P) T bits).bind
          RationalSparsestVertexFairTape.observe := by
    simp only [run,found,Option.bind_some]
    cases RationalSparsestVertexRound.run A w c P (pick A w q P) T bits <;> rfl
  simp only [observed]
  exact RationalSparsestVertexFairTape.run_probability A w c P threshold _ T B Bpositive expected

end
end DirectedFlowCutGap.NormalizedVertexLPRound
