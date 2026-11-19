import DirectedFlowCutGap.EncodedSampledRounding
import DirectedFlowCutGap.RetainedDrawTrees
import DirectedFlowCutGap.RetainedFairBitLaw

/-!
# The charged retained controller with an actual fair-bit sampler

The sampler generates the actual permutation and cell tape. Each draw of
the lowered binary tree increments the charge before the controller
materializes the tape. The projected controller is exactly the existing
lowered tree. The cost theorem uses the concrete word-charge model.
-/

namespace DirectedFlowCutGap.RetainedChargedFairBits

open scoped NNReal
open FiniteDrawTrees LazyFairBitTrees RetainedGridState IntegerAdaptiveExecution

private def countReads {A : Type} (read : ℕ) : FiniteDrawTrees.Tree A → FiniteDrawTrees.Tree (A × ℕ)
  | .pure a => .pure (a, read)
  | .draw n hn next => .draw n hn (fun j => countReads (read + 1) (next j))

private theorem countReads_project {A : Type} (read : ℕ) (tree : FiniteDrawTrees.Tree A) :
    map Prod.fst (countReads read tree) = tree := by
  induction tree generalizing read with
  | pure a => rfl
  | draw n hn next ih =>
    change FiniteDrawTrees.Tree.draw n hn (fun j => map Prod.fst (countReads (read + 1) (next j))) = _
    exact congrArg (FiniteDrawTrees.Tree.draw n hn) (funext fun j => ih j _)

private theorem countReads_binary {A : Type} {tree : FiniteDrawTrees.Tree A}
    (h : LazyFairBitTrees.Binary tree) (read : ℕ) : LazyFairBitTrees.Binary (countReads read tree) := by
  induction h generalizing read with
  | pure a => exact .pure _
  | draw children ih => exact .draw (fun j => ih j _)

private theorem countReads_support {A : Type} {tree : FiniteDrawTrees.Tree A} {bound : ℕ}
    (h : Within bound tree) (read : ℕ) {out : A × ℕ}
    (ha : out ∈ (ideal (countReads read tree)).support) :
    out.2 ≤ read + bound := by
  induction h generalizing read with
  | pure q a =>
    have he : out = (a, read) := (PMF.mem_support_pure_iff _ _).mp ha
    subst out
    simp
  | @draw q n hn next children ih =>
    simp only [countReads, law] at ha
    obtain ⟨j, _, hj⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
    have h := ih j (read + 1) hj
    omega

def sampleCharge (n L T : ℕ) : ℕ := (2 * n * n) * T * RetainedDrawTrees.sampleWidth n L

def sample {n L : ℕ} (T : ℕ) (hL : 0 < L) (a : PairFlags n) :
    FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ) :=
  countReads 0 (lower T (RetainedDrawTrees.sampleTape hL a))

theorem sample_project {n L : ℕ} (T : ℕ) (hL : 0 < L) (a : PairFlags n) :
    map Prod.fst (sample T hL a) = lower T (RetainedDrawTrees.sampleTape hL a) :=
  countReads_project _ _

theorem sample_binary {n L : ℕ} (T : ℕ) (hL : 0 < L) (a : PairFlags n) :
    LazyFairBitTrees.Binary (sample T hL a) :=
  countReads_binary (lower_binary T _) 0

theorem sample_support_bound {n L : ℕ} (T : ℕ) (hL : 0 < L) (a : PairFlags n)
    {out : RetainedTapeInput.Tape L a × ℕ} (ho : out ∈ (ideal (sample T hL a)).support) :
    out.2 ≤ sampleCharge n L T := by
  simpa only [Nat.zero_add, sampleCharge] using
    countReads_support (lower_within (RetainedDrawTrees.sampleTape_within hL a)
      (RetainedDrawTrees.sampleTape_widths hL a) T) 0 ho

private theorem tree_id {A : Type} (a : FiniteDrawTrees.Tree A) : id <$> a = a := by
  induction a with
  | pure a => rfl
  | draw n hn next ih => exact congrArg (FiniteDrawTrees.Tree.draw n hn) (funext ih)

private theorem tree_assoc {A B C : Type} (t : FiniteDrawTrees.Tree A)
    (f : A → FiniteDrawTrees.Tree B) (g : B → FiniteDrawTrees.Tree C) :
    (t >>= f) >>= g = t >>= fun a => f a >>= g := by
  induction t with
  | pure a => rfl
  | draw n hn next ih => exact congrArg (FiniteDrawTrees.Tree.draw n hn) (funext ih)

instance : LawfulMonad FiniteDrawTrees.Tree := LawfulMonad.mk' FiniteDrawTrees.Tree tree_id (by intros; rfl) tree_assoc

private theorem lower_bind {A B : Type} (T : ℕ) (t : FiniteDrawTrees.Tree A) (f : A → FiniteDrawTrees.Tree B) :
    lower T (t >>= f) = lower T t >>= fun a => lower T (f a) := by
  induction t with
  | pure a => rfl
  | draw n hn next ih =>
    change (rejection n hn T >>= fun a => lower T (next a.value >>= f)) =
      (rejection n hn T >>= fun a => lower T (next a.value)) >>= fun a => lower T (f a)
    rw [tree_assoc]
    congr 1
    funext a
    exact ih a.value

private theorem ideal_bind {A B : Type} (t : FiniteDrawTrees.Tree A) (f : A → FiniteDrawTrees.Tree B) :
    ideal (t >>= f) = (ideal t).bind (fun a => ideal (f a)) :=
  law_bind _ t f

private theorem ideal_map {A B : Type} (f : A → B) (t : FiniteDrawTrees.Tree A) :
    ideal (map f t) = (ideal t).map f :=
  law_map _ f t

section Execution

set_option backward.isDefEq.respectTransparency false

variable {n L : ℕ}
variable (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0 < L)
variable {demands : Finset (Pair n)}
local notation "inputGraph" => EncodedIntegerShortestPaths.graph adjacency
local notation "H" => EncodedRoundingState.Witness (demands := demands) adjacency F hL
local notation "Q" => RetainedCandidateSolver.optimizer (demands := demands) adjacency F horder hL
local notation "C" => RetainedGridState.integerCutOracle (G := inputGraph) hL F.base.enumeration
local notation "charged" => EncodedSampledRounding.ChargedResult H

def runWith (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ))
    (R restartFuel epochs : ℕ) (s : Code inputGraph demands L) : FiniteDrawTrees.Tree charged :=
  EncodedSampledRounding.runSampled adjacency F horder hL sampler R restartFuel epochs s

def run (T R restartFuel epochs : ℕ) (s : Code inputGraph demands L) : FiniteDrawTrees.Tree charged :=
  runWith adjacency F horder hL (sample T hL) R restartFuel epochs s

private theorem execute_lower (T R restartFuel epochs : ℕ) (c : Cache H) :
    lower T (RetainedSampledExecution.executeSampled (RetainedDrawTrees.sampleTape hL)
      Q hL C R restartFuel epochs c) =
    RetainedSampledExecution.executeSampled (fun a => lower T (RetainedDrawTrees.sampleTape hL a))
      Q hL C R restartFuel epochs c := by
  induction epochs generalizing c with
  | zero => rfl
  | succ epochs ih =>
    simp only [RetainedSampledExecution.executeSampled]
    split
    · rfl
    · rw [lower_bind]
      congr 1
      funext t
      rw [lower_bind, ih]
      rfl

theorem runWith_projected (T R restartFuel epochs : ℕ) (s : Code inputGraph demands L)
    (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ))
    (hs : ∀ a, map Prod.fst (sampler a) = lower T (RetainedDrawTrees.sampleTape hL a)) :
    map (EncodedSampledRounding.ChargedResult.logged)
        (runWith adjacency F horder hL sampler R restartFuel epochs s) =
      lower T (RetainedDrawTrees.runTree Q hL C R restartFuel epochs s) := by
  have h := EncodedSampledRounding.runData_refines adjacency F horder hL
    sampler R restartFuel epochs s
  change map _ (runWith adjacency F horder hL sampler R restartFuel epochs s) =
    RetainedSampledExecution.runSampled (fun a => map Prod.fst (sampler a))
      Q hL C R restartFuel epochs s at h
  rw [h]
  simp only [hs, RetainedDrawTrees.runTree, RetainedSampledExecution.runSampled, lower_bind,
    execute_lower adjacency F horder hL]
  rfl

theorem run_projected (T R restartFuel epochs : ℕ) (s : Code inputGraph demands L) :
    map (EncodedSampledRounding.ChargedResult.logged) (run adjacency F horder hL T R restartFuel epochs s) =
      lower T (RetainedDrawTrees.runTree Q hL C R restartFuel epochs s) :=
  runWith_projected adjacency F horder hL T R restartFuel epochs s _ (sample_project T hL)

private theorem execute_ideal (R restartFuel epochs : ℕ) (c : Cache H)
    (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ)) :
    ideal (EncodedSampledRounding.executeSampled adjacency F horder hL
      sampler R restartFuel epochs c) =
    EncodedSampledRounding.executeSampled adjacency F horder hL
      (fun a => ideal (sampler a)) R restartFuel epochs c := by
  induction epochs generalizing c with
  | zero => rfl
  | succ epochs ih =>
    simp only [EncodedSampledRounding.executeSampled]
    split
    · rfl
    · rw [ideal_bind]
      congr 1
      funext t
      change ideal (map _ _) = _
      rw [ideal_map, ih]
      rfl

private theorem runWith_ideal (R restartFuel epochs : ℕ) (s : Code inputGraph demands L)
    (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ)) :
    ideal (runWith adjacency F horder hL sampler R restartFuel epochs s) =
    EncodedSampledRounding.runSampled adjacency F horder hL
      (fun a => ideal (sampler a)) R restartFuel epochs s := by
  unfold runWith EncodedSampledRounding.runSampled
  change ideal (map _ _) = _
  rw [ideal_map, execute_ideal adjacency F horder hL]
  rfl

theorem runWith_support_charge (R restartFuel epochs : ℕ) (s : Code inputGraph demands L)
    (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ))
    (K : ℕ) (hK : ∀ a t, t ∈ (ideal (sampler a)).support → t.2 ≤ K) {out : charged}
    (ho : out ∈ (ideal (runWith adjacency F horder hL sampler R restartFuel epochs s)).support) :
    out.operations ≤ EncodedRoundingRuntime.price n L out.logged.result.work +
      EncodedSampledRounding.epochCharge n K * epochs + 1 ∧ out.sampling ≤ K * epochs := by
  rw [runWith_ideal adjacency F horder hL] at ho
  exact EncodedSampledRounding.run_cost_bound adjacency F horder hL _ _ hK R restartFuel epochs s ho

theorem run_support_charge (T R restartFuel epochs : ℕ) (s : Code inputGraph demands L) {out : charged}
    (ho : out ∈ (ideal (run adjacency F horder hL T R restartFuel epochs s)).support) :
    out.operations ≤ EncodedRoundingRuntime.price n L out.logged.result.work +
      EncodedSampledRounding.epochCharge n (sampleCharge n L T) * epochs + 1 ∧
    out.sampling ≤ sampleCharge n L T * epochs :=
  runWith_support_charge adjacency F horder hL R restartFuel epochs s _ _
    (fun a _ ha => sample_support_bound T hL a ha) ho

/-- A bound for every work counter used by the concrete charge function. -/
def workBound (n restartFuel epochs restarts : ℕ) : Work where
  families := 1 + restarts + n * n
  candidates := n * n * (1 + restarts + n * n)
  gates := (epochs + 1) * restartFuel
  epochTests := n * n * epochs
  rounds := n * n
  restarts := restarts
  massScans := 1 + restarts + 2 * (n * n)

theorem runWith_work_bound (T R restartFuel epochs J : ℕ) (hR : 1 < (R : ℝ≥0))
    (s : Code inputGraph demands L) (hJ : (interpret s).mass < (R : ℝ≥0) ^ (J + 1))
    (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ))
    (K : ℕ) (hK : ∀ a t, t ∈ (ideal (sampler a)).support → t.2 ≤ K)
    (hs : ∀ a, map Prod.fst (sampler a) = lower T (RetainedDrawTrees.sampleTape hL a))
    {out : charged} (ho : out ∈ (ideal (runWith adjacency F horder hL sampler R restartFuel epochs s)).support) :
    out.operations ≤ EncodedRoundingRuntime.price n L (workBound n restartFuel epochs J) +
      EncodedSampledRounding.epochCharge n K * epochs + 1 := by
  let : NeZero L := ⟨hL.ne'⟩
  have hmap : out.logged ∈
      (ideal (map EncodedSampledRounding.ChargedResult.logged
        (runWith adjacency F horder hL sampler R restartFuel epochs s))).support := by
    rw [ideal_map]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨out, ho, rfl⟩
  rw [runWith_projected adjacency F horder hL T R restartFuel epochs s sampler hs] at hmap
  have href := lowered_support_subset_ideal T _ hmap
  rw [RetainedFairBitLaw.runTree_law] at href
  obtain ⟨_, _, hr, hj, hf, hc, hg, ht⟩ :=
    RetainedExecutionLaw.sampled_run_work_bounds Q hL C R restartFuel epochs J hR s hJ href
  have hm := (RetainedExecutionLaw.sampled_run_control_bound Q hL C R restartFuel epochs J hR s hJ href).1
  have hactive : (remainingSet s.data.remaining).card ≤ n * n := by
    simpa only [Fintype.card_coe] using RetainedDrawTrees.active_card_le s.data.remaining
  have hround := hr.trans hactive
  have hfamily : out.logged.result.work.families ≤ 1 + J + n * n := by omega
  have hmass : out.logged.result.work.massScans ≤ 1 + J + 2 * (n * n) := by omega
  have hcand : out.logged.result.work.candidates ≤ n * n * (1 + J + n * n) :=
    hc.trans (Nat.mul_le_mul_left _ (by omega))
  have hprice : EncodedRoundingRuntime.price n L out.logged.result.work ≤
      EncodedRoundingRuntime.price n L (workBound n restartFuel epochs J) := by
    simp only [EncodedRoundingRuntime.price, workBound]
    gcongr
  exact (runWith_support_charge adjacency F horder hL R restartFuel epochs s sampler K hK ho).1.trans
    (Nat.add_le_add_right (Nat.add_le_add_right hprice _) _)

theorem run_work_bound (T R restartFuel epochs J : ℕ) (hR : 1 < (R : ℝ≥0))
    (s : Code inputGraph demands L) (hJ : (interpret s).mass < (R : ℝ≥0) ^ (J + 1))
    {out : charged} (ho : out ∈ (ideal (run adjacency F horder hL T R restartFuel epochs s)).support) :
    out.operations ≤ EncodedRoundingRuntime.price n L (workBound n restartFuel epochs J) +
      EncodedSampledRounding.epochCharge n (sampleCharge n L T) * epochs + 1 :=
  runWith_work_bound adjacency F horder hL T R restartFuel epochs J hR s hJ _ _
    (fun a _ ha => sample_support_bound T hL a ha) (sample_project T hL) ho

theorem initial_runWith_work_bound (T : ℕ)
    (sampler : (a : PairFlags n) → FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a × ℕ))
    (K : ℕ) (hK : ∀ a t, t ∈ (ideal (sampler a)).support → t.2 ≤ K)
    (hs : ∀ a, map Prod.fst (sampler a) = lower T (RetainedDrawTrees.sampleTape hL a)) :
    let s := RetainedDemandMask.initial inputGraph F.base.enumeration L hL
    let R := IntegerEpochParameters.restart n
    let fuel := IntegerEpochParameters.fuel n
    ∀ out ∈ (ideal (runWith adjacency F horder hL sampler R (fuel + 1) (fuel + 1) s)).support,
      out.operations ≤ EncodedRoundingRuntime.price n L (workBound n (fuel + 1) (fuel + 1) fuel) +
        EncodedSampledRounding.epochCharge n K * (fuel + 1) + 1 := by
  dsimp only
  intro out ho
  have hm :
      (interpret (RetainedDemandMask.initial inputGraph F.base.enumeration L hL)).mass <
        (IntegerEpochParameters.restart n : ℝ≥0) ^ (IntegerEpochParameters.fuel n + 1) := by
    rw [RetainedDemandMask.initial, RetainedClosureLaw.initialMaskedCode_mass]
    simpa only [Fintype.card_fin] using IntegerClosureAsymptotic.initial_fuel_bound inputGraph L hL
  exact runWith_work_bound adjacency F horder hL T _ _ _ _
    (IntegerClosureAsymptotic.restart_nnreal_one_lt n) _ hm sampler K hK hs ho

theorem initial_work_bound (T : ℕ) :
    let s := RetainedDemandMask.initial inputGraph F.base.enumeration L hL
    let R := IntegerEpochParameters.restart n
    let fuel := IntegerEpochParameters.fuel n
    ∀ out ∈ (ideal (run adjacency F horder hL T R (fuel + 1) (fuel + 1) s)).support,
      out.operations ≤ EncodedRoundingRuntime.price n L (workBound n (fuel + 1) (fuel + 1) fuel) +
        EncodedSampledRounding.epochCharge n (sampleCharge n L T) * (fuel + 1) + 1 :=
  initial_runWith_work_bound adjacency F horder hL T _ _
    (fun a _ ha => sample_support_bound T hL a ha) (sample_project T hL)

end Execution

end DirectedFlowCutGap.RetainedChargedFairBits
