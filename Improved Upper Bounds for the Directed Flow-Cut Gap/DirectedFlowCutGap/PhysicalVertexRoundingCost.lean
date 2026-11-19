import DirectedFlowCutGap.PhysicalVertexRounding
import DirectedFlowCutGap.PhysicalIntegerRoundingCost

/-! Compose the recorded work of the realized vertex reductions with the
packed controller and its binary cut readback. -/

namespace DirectedFlowCutGap.PhysicalVertexRoundingCost

open BinaryArithmetic RetainedGridState Polynomial
open EncodedUnitCostReplication IntegralNetworkFlow.Tabulated
open PhysicalIntegerRoundingCost (roundBudget eval_mono)

noncomputable def uniformBudget (p : Polynomial ℕ) (n T : ℕ) : ℕ :=
  3000*n^2+1142*n+121+p.eval (6*n+T)

theorem uniformBudget_mono (p : Polynomial ℕ) {n m : ℕ} (size : n ≤ m) (T : ℕ) :
    uniformBudget p n T ≤ uniformBudget p m T := by
  have hp := eval_mono p (Nat.add_le_add_right (Nat.mul_le_mul_left 6 size) T)
  unfold uniformBudget
  gcongr

section Uniform

open EncodedUniformWeightParameters EncodedUniformChain EncodedUniformOutput RawNonnegativeRational

theorem uniform_paid (p : Polynomial ℕ) (bounds : ∀ n L T, roundBudget n L T ≤ p.eval (n+T))
    {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) {r : PhysicalIntegerRounding.Result n}
    (run : PhysicalVertexRounding.uniform T D tape = some r) : r.paid ≤ uniformBudget p n T := by
  by_cases positive : Code.one.le (compute D).total = true
  · let chain := expand D
    change (if Code.one.le (compute D).total = true then
      (PhysicalIntegerRounding.run T chain.data.adjacency chain.cutoff tape).map
        (PhysicalVertexRounding.project (originalMaskWithCost chain) ((compute D).work+chain.work+10))
      else some ⟨Vector.replicate n false,tape,(compute D).work+4*n+10⟩) = some r at run
    rw [ite_eq_left positive] at run
    cases native : PhysicalIntegerRounding.run T chain.data.adjacency chain.cutoff tape with
    | none => simp [native] at run
    | some x =>
      simp only [native,Option.map_some,Option.some.injEq] at run
      have mass : 0<(compute D).total.realValue := by
        rw [compute_total]
        exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp positive)
      have material := computed_work_bound D mass
      have unpack := computed_originalMask_work D mass x.mask
      have small := expand_size_bound D mass
      have paid := (PhysicalIntegerRoundingCost.round_paid (expand_cutoff_bounds D positive).1 tape native).trans
        ((bounds _ _ _).trans (eval_mono p (Nat.add_le_add_right small T)))
      rw [← run]
      change (compute D).work+chain.work+10+x.paid+(originalMaskWithCost chain x.mask).2 ≤ _
      rw [compute_work]
      unfold uniformBudget
      change chain.work ≤ _ at material
      change (originalMaskWithCost chain x.mask).2 ≤ _ at unpack
      omega
  · simp only [PhysicalVertexRounding.uniform,ite_eq_right positive,Option.some.injEq] at run
    rw [← run]
    dsimp only
    rw [compute_work]
    unfold uniformBudget
    omega

end Uniform

noncomputable def weightedBudget (p : Polynomial ℕ) (n T : ℕ) : ℕ :=
  9*n^2*(CountedSearch.searchBound (3*n) 24+224)+640*n^4+108*n^3+316*n^2+1011*n+206+
    uniformBudget p (4*n^2) T

theorem weightedBudget_mono (p : Polynomial ℕ) {n m : ℕ} (size : n ≤ m) (T : ℕ) :
    weightedBudget p n T ≤ weightedBudget p m T := by
  unfold weightedBudget CountedSearch.searchBound CountedSearch.visitBound
  gcongr
  exact uniformBudget_mono p (by gcongr) T

section Weighted

open EncodedUnitCostPreparation

theorem weighted_paid (p : Polynomial ℕ) (bounds : ∀ n L T, roundBudget n L T ≤ p.eval (n+T))
    {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) {r : PhysicalIntegerRounding.Result n}
    (run : PhysicalVertexRounding.weighted T D tape = some r) : r.paid ≤ weightedBudget p n T := by
  have prep := prepareAndReduce_work D
  unfold PhysicalVertexRounding.weighted at run
  dsimp only at run
  rw [show (prepareAndReduce D).reduced=(build D).data.reduce from rfl] at run
  by_cases zero : (build D).data.totals.objective.num=0
  · rw [Input.reduce_zero _ zero] at run
    simp only [Option.some.injEq] at run
    have unpack := pullback_work_bound D (build D).data.zeroMask
    rw [← run]
    change (prepareAndReduce D).work+((build D).pullbackMaskWithCost (build D).data.zeroMask).2+5 ≤ _
    unfold weightedBudget
    omega
  · rw [Input.reduce_positive _ zero] at run
    have pos : 0<n := by
      by_contra hn
      obtain rfl : n=0 := by omega
      exact zero (empty_objective_zero D)
    let pre := build D
    let clone := materialize pre.data pre.data.counts
    change ((PhysicalVertexRounding.uniform T clone.input tape).map
      (PhysicalVertexRounding.project (pre.pullbackSampleWithCost pre.data.counts clone)
        ((prepareAndReduce D).work+5))) = some r at run
    cases natRun : PhysicalVertexRounding.uniform T clone.input tape with
    | none => simp [natRun] at run
    | some x =>
      simp only [natRun,Option.map_some,Option.some.injEq] at run
      have paid := (uniform_paid p bounds T clone.input tape natRun).trans
        (uniformBudget_mono p (build_clone_count D pos zero) T)
      have unpack := pullbackSample_work_bound D pos zero x.mask
      rw [← run]
      change (prepareAndReduce D).work+5+x.paid+(pre.pullbackSampleWithCost pre.data.counts clone x.mask).2 ≤ _
      change (pre.pullbackSampleWithCost pre.data.counts clone x.mask).2 ≤ _ at unpack
      unfold weightedBudget
      omega

end Weighted

noncomputable def sizeBudget (p : Polynomial ℕ) (n T : ℕ) : ℕ :=
  60*n^2+188*n+97+weightedBudget p n T

section Size

open EncodedHeavyVertexPreparation EncodedCubeRootThreshold

theorem size_paid (p : Polynomial ℕ) (bounds : ∀ n L T, roundBudget n L T ≤ p.eval (n+T))
    {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) {r : PhysicalIntegerRounding.Result n}
    (run : PhysicalVertexRounding.size T D tape = some r) : r.paid ≤ sizeBudget p n T := by
  let prep := prepare D
  change ((PhysicalVertexRounding.weighted T prep.1.data tape).map
    (PhysicalVertexRounding.project (combinedMaskWithCost prep.1) (prep.2+5))) = some r at run
  cases native : PhysicalVertexRounding.weighted T prep.1.data tape with
  | none => simp [native] at run
  | some x =>
    simp only [native,Option.map_some,Option.some.injEq] at run
    have setup := prepare_work D
    have unpack := build_combinedMask_work D (threshold n) x.mask
    have small : prep.1.size ≤ n := build_size_le D (threshold n)
    have paid := (weighted_paid p bounds T prep.1.data tape native).trans (weightedBudget_mono p small T)
    rw [← run]
    change prep.2+5+x.paid+(combinedMaskWithCost prep.1 x.mask).2 ≤ _
    change prep.2 ≤ _ at setup
    change (combinedMaskWithCost prep.1 x.mask).2 ≤ _ at unpack
    unfold sizeBudget
    omega

end Size

/-- A single polynomial bounds either reduction at any smaller graph or trial count. -/
theorem polynomial_bound : ∃ q : Polynomial ℕ, ∀ n T x, n ≤ x → T ≤ x →
    (∀ (D : Input n) tape r, PhysicalVertexRounding.weighted T D tape = some r → r.paid ≤ q.eval x) ∧
    (∀ (D : Input n) tape r, PhysicalVertexRounding.size T D tape = some r → r.paid ≤ q.eval x) := by
  obtain ⟨p,hp⟩ := PhysicalIntegerRoundingCost.round_budget_polynomial
  let a : Polynomial ℕ := C 3*X
  let search := a*(a*(a*(C 24+C 17)+C 18+C 4)+C 5)+C 17*a+C 21
  let m : Polynomial ℕ := C 4*X^2
  let uniform := C 3000*m^2+C 1142*m+C 121+p.comp (C 6*m+X)
  let weighted := C 9*X^2*(search+C 224)+C 640*X^4+C 108*X^3+C 316*X^2+C 1011*X+C 206+uniform
  let q := C 60*X^2+C 188*X+C 97+weighted
  refine ⟨q,fun n T x hn ht => ?_⟩
  have mono : sizeBudget p n T ≤ sizeBudget p x x := by
    have h := eval_mono p (show 6*(4*n^2)+T ≤ 6*(4*x^2)+x by gcongr)
    unfold sizeBudget weightedBudget uniformBudget CountedSearch.searchBound CountedSearch.visitBound
    gcongr
  have eval : q.eval x = sizeBudget p x x := by
    simp only [q,weighted,uniform,search,a,m,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_comp,
      sizeBudget,weightedBudget,uniformBudget,CountedSearch.searchBound,CountedSearch.visitBound]
  rw [eval]
  refine ⟨fun D tape r run => (weighted_paid p hp T D tape run).trans ?_,
    fun D tape r run => (size_paid p hp T D tape run).trans mono⟩
  exact (Nat.le_add_left _ _).trans mono

end DirectedFlowCutGap.PhysicalVertexRoundingCost
