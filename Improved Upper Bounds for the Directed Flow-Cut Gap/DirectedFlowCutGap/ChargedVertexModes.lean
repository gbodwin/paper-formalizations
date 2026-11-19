import DirectedFlowCutGap.ChargedPhysicalVertexSolver

/-!
# The mass and size vertex modes with their composed charges

The two executable entry points take typed input, a confidence exponent
and a finite bit tape. The measured price width includes stored padding.
The exact observation transports the earlier cut and confidence guarantees.
-/

namespace DirectedFlowCutGap.ChargedVertexModes

open BinaryArithmetic BinaryFractionalRows BinaryRational FiniteDrawTrees LazyFairBitTrees
open EncodedVertexSolver EncodedVertexAmplification
open ChargedPhysicalVertexSolver (ChargedRound Result)

inductive Mode where
  | mass
  | size

def round (n : ℕ) : Mode → Rounding n
  | .mass => EncodedWeightedRounding.tree
  | .size => EncodedSizeRounding.tree

def chargedRound (n : ℕ) : Mode → ChargedRound n
  | .mass => ChargedWeightedRounding.bitTree
  | .size => ChargedSizeRounding.bitTree

def roundBudget (n T : ℕ) : Mode → ℕ
  | .mass => ChargedWeightedRounding.budget n T
  | .size => ChargedSizeRounding.budget n T

theorem chargedRound_value {n : ℕ} (mode : Mode) (T : ℕ) (r : RoundingInput n) :
    map Prod.fst (chargedRound n mode T r) = lower T (round n mode r) := by
  cases mode
  · exact ChargedWeightedRounding.bitTree_value T r
  · exact ChargedSizeRounding.bitTree_value T r

theorem chargedRound_charge {n : ℕ} (mode : Mode) (T : ℕ) (r : RoundingInput n) :
    ∀ a ∈ (ideal (chargedRound n mode T r)).support, a.2 ≤ roundBudget n T mode := by
  intro a ha
  cases mode
  · exact ChargedWeightedRounding.bitTree_charge T r ha
  · exact ChargedSizeRounding.bitTree_charge T r ha

def priceWidth {n : ℕ} (D : BinaryFractionalGuesses.Input n) : ℕ :=
  LambdaRowProgram.rowBits D.costs.toList + 1

theorem priceWidth_positive {n : ℕ} (D : BinaryFractionalGuesses.Input n) : 1 ≤ priceWidth D :=
  Nat.le_add_left 1 _

theorem priceWidth_bounds {n : ℕ} (D : BinaryFractionalGuesses.Input n) (i : Fin n) :
    StoredBounded (get D.costs i) (priceWidth D) := by
  have hm : get D.costs i ∈ D.costs.toList := by
    change D.costs[i.val] ∈ D.costs.toList
    have hi : i.val < D.costs.toList.length := by simp [i.isLt]
    simpa only [Vector.getElem_toList] using List.getElem_mem hi
  have h := LambdaRowProgram.member_bits hm
  unfold StoredBounded priceWidth
  omega

def run {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) (tape : Bits) :
    Option (Result n) :=
  let e := confidenceExponent n κ
  ChargedPhysicalVertexSolver.run D (chargedRound n mode) (roundDrawBound n) e (e + 1) tape

def budget {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) : ℕ :=
  let e := confidenceExponent n κ
  let G := BinaryFractionalGuesses.decodeInput D
  let T := ChargedPhysicalVertexSolver.trialLimit G (roundDrawBound n) e (e + 1)
  ChargedPhysicalVertexSolver.budget G (priceWidth D) e (roundBudget n T mode)

theorem run_value {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) (tape : Bits) :
    (run κ mode D tape).map Result.observe =
      EncodedSolverBits.run (polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n mode)) tape :=
  ChargedPhysicalVertexSolver.run_value D (round n mode) (chargedRound n mode) _ _ _ tape (chargedRound_value mode)

theorem run_charges {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) (tape : Bits)
    {out : Result n} (ho : run κ mode D tape = some out) :
    out.dispatch ≤ PhysicalSolverCharges.dispatchBudget D ∧
      out.lookups ≤ PhysicalSolverCharges.lookupBudget D ∧
      out.roundingAndSelection ≤ budget κ mode D :=
  ChargedPhysicalVertexSolver.run_charges D (round n mode) (chargedRound n mode) _ _ _ _ tape
    (chargedRound_value mode) (priceWidth_positive D) (priceWidth_bounds D) (chargedRound_charge mode _) ho

private theorem max_fold_le (B : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ B) :
    xs.foldr max 0 ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem inputWidth_le {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    FractionalCoverRawCore.inputWidth (BinaryFractionalGuesses.decodeInput D).costs ≤ priceWidth D := by
  change FractionalCoverRawCore.inputWidth (decodeRow D.costs) ≤ _
  rw [← BinaryFractionalGuesses.inputWidth_value, BinaryFractionalGuesses.inputWidth,
    BinaryFractionalGuesses.widthList_value]
  apply max_fold_le
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hw := LambdaRowProgram.member_bits ha
  have hn := Nat.size_le.mpr (value_lt a.num)
  have hd := Nat.size_le.mpr (value_lt a.den)
  simp only [decode]
  unfold priceWidth
  exact max_le (hn.trans (by omega)) (hd.trans (by omega))

private theorem roundBudget_mono_trials (n : ℕ) (mode : Mode) {T T' : ℕ} (h : T ≤ T') :
    roundBudget n T mode ≤ roundBudget n T' mode := by
  cases mode <;> unfold roundBudget ChargedSizeRounding.budget ChargedWeightedRounding.budget
    ChargedUniformRounding.budget PreparedIntegerController.budget ChargedIntegerRounding.budget
    RetainedBinarySampler.wordBudget EncodedSampledRounding.epochCharge BinaryDrawTreeExecution.oneDrawBound
  all_goals dsimp only; gcongr

/-- A polynomial envelope in the vertex count, the total stored price
width plus one, and the requested confidence exponent. -/
def dimensionBudget (n B κ : ℕ) (mode : Mode) : ℕ :=
  let E := (n + 2) * κ + 1
  let R := 2*B + 2*(n+1) + 3
  let T := E * (R * roundDrawBound n) + 1 + E
  ChargedAmplification.budget E n B
    (ChargedPhysicalVertexSolver.sampleBudget n B R (roundBudget n T mode))

theorem budget_le {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) :
    budget κ mode D ≤ dimensionBudget n (priceWidth D) κ mode := by
  let e := confidenceExponent n κ
  let G := BinaryFractionalGuesses.decodeInput D
  let B := priceWidth D
  let E := (n + 2) * κ + 1
  let R := 2*B + 2*(n+1) + 3
  let T := E * (R * roundDrawBound n) + 1 + E
  have he : e + 1 ≤ E := by
    have hlog := Nat.log_le_self 2 (max 1 n)
    have hmax : max 1 n ≤ n + 1 := max_le (by omega) (by omega)
    rw [← Nat.log2_eq_log_two] at hlog
    have hwidth : FairBitWords.width (max 1 n) ≤ n + 2 := by
      unfold FairBitWords.width
      omega
    exact Nat.add_le_add_right (Nat.mul_le_mul_right κ hwidth) 1
  have hr : ChargedPhysicalVertexSolver.rowLimit G ≤ R := by
    have hw : FractionalCoverRawCore.inputWidth G.costs ≤ B := inputWidth_le D
    have hs : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
    unfold ChargedPhysicalVertexSolver.rowLimit FractionalCoverGuesses.gridSteps R
    omega
  have hT : ChargedPhysicalVertexSolver.trialLimit G (roundDrawBound n) e (e + 1) ≤ T := by
    unfold ChargedPhysicalVertexSolver.trialLimit T
    apply (FairBitConfidence.trials_le ..).trans
    change (e + 1) * (ChargedPhysicalVertexSolver.rowLimit G * roundDrawBound n) + 1 +
      (e + 1) ≤ _
    gcongr
  have hc := roundBudget_mono_trials n mode hT
  have he' : e ≤ E := by omega
  change ChargedPhysicalVertexSolver.budget G B e
    (roundBudget n (ChargedPhysicalVertexSolver.trialLimit G (roundDrawBound n) e (e + 1)) mode) ≤
    ChargedAmplification.budget E n B (ChargedPhysicalVertexSolver.sampleBudget n B R (roundBudget n T mode))
  unfold ChargedPhysicalVertexSolver.budget ChargedAmplification.budget
    ChargedPhysicalVertexSolver.sampleBudget ChargedCutSelection.rowBound BinaryCutPriceSelection.selectionBound
  gcongr

private theorem within {n : ℕ} (κ : ℕ) (mode : Mode) (G : GraphInput n) :
    Within (EncodedSolverBits.vertexBudget κ G) (polynomialBitTree κ G (round n mode)) := by
  cases mode
  · exact EncodedSolverBits.vertex_mass_within κ G
  · exact EncodedSolverBits.vertex_size_within κ G

theorem run_fairTape {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) :
    let G := BinaryFractionalGuesses.decodeInput D
    (EncodedSolverBits.fairTape (EncodedSolverBits.vertexBudget κ G)).map
      (fun tape => (run κ mode D tape).map Result.output) =
      (ideal (polynomialBitTree κ G (round n mode))).map some := by
  dsimp only
  rw [← EncodedSolverBits.run_fairTape (within κ mode _) (EncodedAmplification.bitTree_binary ..)]
  congr 1
  funext tape
  have h := congrArg (Option.map Prod.fst) (run_value κ mode D tape)
  simpa only [Option.map_map, Function.comp_def, Result.observe] using h

theorem run_complete {n : ℕ} (κ : ℕ) (mode : Mode) (D : BinaryFractionalGuesses.Input n) (tape : Bits)
    (hlen : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    let G := BinaryFractionalGuesses.decodeInput D
    ∃ r used, run κ mode D tape = some r ∧ r.tape = (tape.drop used, used) ∧
      used ≤ EncodedSolverBits.vertexBudget κ G ∧ Valid G r.output ∧
      r.dispatch ≤ PhysicalSolverCharges.dispatchBudget D ∧
      r.lookups ≤ PhysicalSolverCharges.lookupBudget D ∧ r.roundingAndSelection ≤ budget κ mode D := by
  let G := BinaryFractionalGuesses.decodeInput D
  let t := polynomialBitTree κ G (round n mode)
  have hw : Within (EncodedSolverBits.vertexBudget κ G) t := within κ mode G
  have hb : Binary t := EncodedAmplification.bitTree_binary ..
  obtain ⟨a, used, he, hused⟩ := EncodedSolverBits.complete hw hb tape hlen
  have hs := EncodedSolverBits.run_support hb he
  have hv : Valid G a := by
    cases mode
    · exact massBit_support_valid _ _ G hs
    · exact sizeBit_support_valid _ _ G hs
  have hrun := run_value κ mode D tape
  change (run κ mode D tape).map Result.observe = EncodedSolverBits.run t tape at hrun
  rw [he] at hrun
  obtain ⟨r, hr, hresult⟩ := Option.map_eq_some_iff.mp hrun
  have hout : r.output = a := congrArg Prod.fst hresult
  have htape : r.tape = (tape.drop used, used) := congrArg Prod.snd hresult
  obtain ⟨hdisp, hlook, hwork⟩ := run_charges κ mode D tape hr
  exact ⟨r, used, hr, htape, hused, hout ▸ hv, hdisp, hlook, hwork⟩

end DirectedFlowCutGap.ChargedVertexModes
