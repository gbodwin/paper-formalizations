import DirectedFlowCutGap.ChargedAmplification
import DirectedFlowCutGap.ChargedSizeRounding
import DirectedFlowCutGap.PhysicalSolverChargeBounds

/-!
# Composed charges for the physical vertex solver

The fixed fractional dispatch and retained heap readback run once. Their
cover rows feed the prepared rounder, binary row selection and binary
amplification. All draws use the original global rejection limit.

The two physical-prefix charges and the modeled charges of the typed
rounding and selection pipeline are returned separately.
-/

namespace DirectedFlowCutGap.ChargedPhysicalVertexSolver

open BinaryArithmetic BinaryFractionalRows BinaryRational FiniteDrawTrees LazyFairBitTrees
open EncodedVertexSolver EncodedVertexAmplification PhysicalCoverReader
open RetainedGridState (Flags)

abbrev ChargedRound (n : ℕ) := ℕ → RoundingInput n → FiniteDrawTrees.Tree (Flags n × ℕ)

def treeFromPlan {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : ChargedRound n) (T : ℕ) : Plan n → FiniteDrawTrees.Tree (Output n × ℕ)
  | .infeasible d => .pure (.infeasible d, 4*n+10)
  | .zero mask => .pure (.cut mask, 4*n+10)
  | .invalid => .pure (.invalid, 4*n+10)
  | .covers rows =>
    let G := BinaryFractionalGuesses.decodeInput D
    map (fun result => ((ChargedCutSelection.result result).elim .invalid .cut, result.2 + 4*n+10))
      (ChargedCutSelection.best D.costs (rows.map (fun y => round T (roundingInput G y))))

theorem treeFromPlan_value {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : Rounding n) (charged : ChargedRound n) (T : ℕ)
    (href : ∀ r, map Prod.fst (charged T r) = lower T (round r)) (p : Plan n) :
    map Prod.fst (treeFromPlan D charged T p) =
      lower T (PhysicalVertexSolver.treeFromPlan (BinaryFractionalGuesses.decodeInput D) round p) := by
  cases p with
  | invalid | infeasible _ => rfl
  | zero mask =>
    have hz : maskOfSet (column mask) = mask := by
      apply Vector.ext
      intro i hi
      simp [maskOfSet, column]
    simp only [treeFromPlan, PhysicalVertexSolver.treeFromPlan, roundOutput, hz]
    rfl
  | covers rows =>
    let G := BinaryFractionalGuesses.decodeInput D
    let convert (a : Option (Flags n)) : Output n := a.elim .invalid .cut
    let cs := ChargedCutSelection.best D.costs (rows.map (fun y => charged T (roundingInput G y)))
    change Prod.fst <$> ((fun a => (convert (ChargedCutSelection.result a), a.2 + 4*n+10)) <$> cs) =
      lower T (convert <$> EncodedCutSelection.best (decodeRow D.costs) (rows.map (fun y => round (roundingInput G y))))
    rw [← ChargedUniformRounding.map_lower, ChargedCutSelection.lower_best]
    have h := ChargedCutSelection.best_value D.costs (rows.map (fun y => charged T (roundingInput G y)))
    change ChargedCutSelection.result <$> cs = _ at h
    simp only [List.map_map, Function.comp_def, href] at h ⊢
    rw [← h]
    simp only [Functor.map_map]

def rowLimit {n : ℕ} (G : GraphInput n) : ℕ :=
  FractionalCoverGuesses.gridSteps n (FractionalCoverRawCore.inputWidth G.costs) + 1

def rowsCount {n : ℕ} : Plan n → ℕ
  | .covers rows => rows.length
  | _ => 0

theorem rowsCount_le {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    rowsCount (plan (BinaryFractionalGuesses.solveInput D).1) ≤ rowLimit (BinaryFractionalGuesses.decodeInput D) := by
  have hc := BinaryFractionalGuesses.solveInput_correct D
  cases h : (BinaryFractionalGuesses.solveInput D).1 with
  | covers ss =>
    simp only [h, FractionalCoverRawGuesses.Correct, BinaryFractionalGuesses.decodeOutput,
      FractionalCoverRawGuesses.decodeOutput, List.length_map] at hc
    simp only [plan, rowsCount, rowLimit, List.length_map]
    exact Nat.le_of_eq hc.1
  | invalid | infeasible _ | zero _ => exact Nat.zero_le _

def sampleBudget (n B rows roundBudget : ℕ) : ℕ :=
  rows * ChargedCutSelection.rowBound n B roundBudget + 1 + 4*n+10

theorem treeFromPlan_charge {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (charged : ChargedRound n) (T : ℕ) (p : Plan n) (roundBudget : ℕ) (hB : 1 ≤ B)
    (hc : ∀ i, StoredBounded (get D.costs i) B)
    (hr : ∀ r a, a ∈ (ideal (charged T r)).support → a.2 ≤ roundBudget)
    {out : Output n × ℕ} (ho : out ∈ (ideal (treeFromPlan D charged T p)).support) :
    out.2 ≤ sampleBudget n B (rowsCount p) roundBudget := by
  cases p with
  | invalid | infeasible _ | zero _ =>
    simp only [treeFromPlan, ideal, law, PMF.support_pure, Set.mem_singleton_iff] at ho
    rw [ho]
    simp [sampleBudget, rowsCount]
  | covers rows =>
    let G := BinaryFractionalGuesses.decodeInput D
    let ts := rows.map (fun y => charged T (roundingInput G y))
    simp only [treeFromPlan, ideal, law_map] at ho
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    have hround : ∀ t ∈ ts, ∀ a ∈ (ideal t).support, a.2 ≤ roundBudget := by
      rintro t ht x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp ht
      exact hr _ x hx
    have h := (ChargedCutSelection.best_charge D.costs ts roundBudget hB hc hround ha).2
    simp only [ts, List.length_map] at h
    simp only [sampleBudget, rowsCount]
    omega

def trialLimit {n : ℕ} (G : GraphInput n) (roundBound extra confidence : ℕ) : ℕ :=
  FairBitConfidence.trials ((extra + 1) * drawBound G roundBound) confidence

def amplifiedFromPlan {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : ChargedRound n) (roundBound extra confidence : ℕ) (p : Plan n) :
    FiniteDrawTrees.Tree (Output n × ℕ) :=
  let T := trialLimit (BinaryFractionalGuesses.decodeInput D) roundBound extra confidence
  ChargedAmplification.tree D.costs (treeFromPlan D round T p) extra

theorem amplifiedFromPlan_value {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : Rounding n) (charged : ChargedRound n) (roundBound extra confidence : ℕ)
    (href : ∀ T r, map Prod.fst (charged T r) = lower T (round r)) (p : Plan n) :
    let G := BinaryFractionalGuesses.decodeInput D
    map Prod.fst (amplifiedFromPlan D charged roundBound extra confidence p) =
      EncodedAmplification.bitTree (codePrice G) (PhysicalVertexSolver.treeFromPlan G round p)
        (drawBound G roundBound) extra confidence := by
  dsimp only
  rw [amplifiedFromPlan, ChargedAmplification.tree_value, treeFromPlan_value D round charged _ (href _) p]
  let G := BinaryFractionalGuesses.decodeInput D
  let T := trialLimit G roundBound extra confidence
  let base := PhysicalVertexSolver.treeFromPlan G round p
  let choose := EncodedAmplification.minimum (codePrice G) extra
  change choose <$> EncodedAmplification.samples (lower T base) (extra + 1) =
    lower T (choose <$> EncodedAmplification.samples base (extra + 1))
  rw [← ChargedUniformRounding.map_lower, ChargedAmplification.lower_samples]

def prepare {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : ChargedRound n)
    (roundBound extra confidence : ℕ) : Option (FiniteDrawTrees.Tree (Output n × ℕ) × ℕ × ℕ) :=
  (PhysicalSourceReadback.run D).map fun (p, paid, read) =>
    (amplifiedFromPlan D round roundBound extra confidence p, paid, read)

structure Result (n : ℕ) where
  output : Output n
  tape : EncodedSolverBits.Tape
  dispatch : ℕ
  lookups : ℕ
  roundingAndSelection : ℕ

def Result.observe {n : ℕ} (r : Result n) : Output n × EncodedSolverBits.Tape :=
  (r.output, r.tape)

def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : ChargedRound n)
    (roundBound extra confidence : ℕ) (tape : Bits) : Option (Result n) := do
  let (t, paid, lookup) ← prepare D round roundBound extra confidence
  let ((a, work), rest) ← EncodedSolverBits.run t tape
  pure ⟨a, rest, paid, lookup, work⟩

theorem run_value {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Rounding n)
    (charged : ChargedRound n) (roundBound extra confidence : ℕ) (tape : Bits)
    (href : ∀ T r, map Prod.fst (charged T r) = lower T (round r)) :
    (run D charged roundBound extra confidence tape).map Result.observe =
      EncodedSolverBits.run (boundedBitTree roundBound extra confidence
        (BinaryFractionalGuesses.decodeInput D) round) tape := by
  obtain ⟨paid, lookup, hp, _, _⟩ := PhysicalSourceReadback.run_eq D
  let p := plan (BinaryFractionalGuesses.solveInput D).1
  let t := amplifiedFromPlan D charged roundBound extra confidence p
  have hv : map Prod.fst t = boundedBitTree roundBound extra confidence (BinaryFractionalGuesses.decodeInput D) round := by
    simpa only [t, p, PhysicalVertexSolver.treeFromPlan_eq, BinaryFractionalGuesses.solveInput_refines,
      boundedBitTree, boundedFromOutput] using amplifiedFromPlan_value D round charged roundBound extra confidence href p
  rw [← hv, EncodedSolverBits.run_map]
  have hprep : prepare D charged roundBound extra confidence = some (t, paid, lookup) := by simp [prepare, hp, t, p]
  cases ht : EncodedSolverBits.run t tape with
  | none => simp [run, hprep, ht]
  | some result =>
    rcases result with ⟨⟨a, work⟩, rest⟩
    simp [run, hprep, ht, Result.observe]

private theorem binary_of_map {A B : Type} {f : A → B} {t : FiniteDrawTrees.Tree A}
    (h : Binary (map f t)) : Binary t := by
  induction t with
  | pure a => exact .pure a
  | draw n hn next ih =>
    change Binary (.draw n hn (fun j => map f (next j))) at h
    cases h with
    | draw children => exact .draw (fun j => ih j (children j))

def budget {n : ℕ} (G : GraphInput n) (B extra roundBudget : ℕ) : ℕ :=
  ChargedAmplification.budget extra n B (sampleBudget n B (rowLimit G) roundBudget)

theorem run_charges {n B : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Rounding n)
    (charged : ChargedRound n) (roundBound extra confidence roundBudget : ℕ) (tape : Bits)
    (href : ∀ T r, map Prod.fst (charged T r) = lower T (round r))
    (hB : 1 ≤ B) (hc : ∀ i, StoredBounded (get D.costs i) B)
    (hr : ∀ r a, a ∈ (ideal (charged (trialLimit (BinaryFractionalGuesses.decodeInput D)
      roundBound extra confidence) r)).support → a.2 ≤ roundBudget)
    {out : Result n} (ho : run D charged roundBound extra confidence tape = some out) :
    out.dispatch ≤ PhysicalSolverCharges.dispatchBudget D ∧
      out.lookups ≤ PhysicalSolverCharges.lookupBudget D ∧
      out.roundingAndSelection ≤ budget (BinaryFractionalGuesses.decodeInput D) B extra roundBudget := by
  obtain ⟨paid, lookup, hp, hd, hl⟩ := PhysicalSourceReadback.run_eq D
  let G := BinaryFractionalGuesses.decodeInput D
  let p := plan (BinaryFractionalGuesses.solveInput D).1
  let T := trialLimit G roundBound extra confidence
  let t := amplifiedFromPlan D charged roundBound extra confidence p
  have hv := amplifiedFromPlan_value D round charged roundBound extra confidence href p
  have hb : Binary t := binary_of_map (hv.symm ▸ EncodedAmplification.bitTree_binary ..)
  have hprep : prepare D charged roundBound extra confidence = some (t, paid, lookup) := by simp [prepare, hp, t, p]
  cases ht : EncodedSolverBits.run t tape with
  | none => simp [run, hprep, ht] at ho
  | some result =>
    rcases result with ⟨⟨a, work⟩, rest⟩
    have hout : out = ⟨a, rest, paid, lookup, work⟩ := by simpa [run, hprep, ht] using ho.symm
    subst out
    have hs := EncodedSolverBits.run_support hb ht
    change (a, work) ∈ (ideal (ChargedAmplification.tree D.costs (treeFromPlan D charged T p) extra)).support at hs
    have hsample : ∀ x ∈ (ideal (treeFromPlan D charged T p)).support,
        x.2 ≤ sampleBudget n B (rowLimit G) roundBudget := by
      intro x hx
      apply (treeFromPlan_charge D charged T p roundBudget hB hc hr hx).trans
      have hrows := rowsCount_le D
      unfold sampleBudget
      gcongr
    exact ⟨hd, hl, ChargedAmplification.tree_charge D.costs _ extra _ hB hc hsample hs⟩

end DirectedFlowCutGap.ChargedPhysicalVertexSolver
