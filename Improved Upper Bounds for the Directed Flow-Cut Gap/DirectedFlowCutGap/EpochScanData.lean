import DirectedFlowCutGap.AdaptiveRoundRefreshProgram
import DirectedFlowCutGap.EpochScanHeadProgram

/-! The physical epoch scan retains the exact cache and consumes a prefix of the sampled order. -/

namespace DirectedFlowCutGap.EpochScanData

open BinaryArithmetic RetainedGridState IntegralNetworkFlow ImmutableReferenceSimulation
open CandidateEnumeration (Node Network)
open AdaptiveControllerStorage (CacheAt)

variable {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}

abbrev Graph (a : PairFlags n) := EncodedIntegerShortestPaths.graph a

noncomputable abbrev optimizer (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) :=
  tabulatedOptimizer (G:=Graph adj) (D:=demands) positive (ResidualSearch.Enumeration.fin n) E

noncomputable abbrev cacheOf (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (s : Code (Graph adj) demands L) :=
  refresh (optimizer (adj:=adj) (demands:=demands) positive E) s

@[simp] theorem cacheOf_state (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L))
    (s : Code (Graph adj) demands L) : (cacheOf positive E s).state=s := rfl

abbrev cutOracle (adj : PairFlags n) (positive : 0<L) :=
  EncodedRoundingInput.cutOracle (EpochSelectedRoundProgram.enumeration n) adj positive

noncomputable abbrev candidateWords (EN : ResidualSearch.Enumeration (Node n L))
    (E : ResidualSearch.Enumeration (Network n L)) (s : Code (Graph adj) demands L) :=
  CandidateFamilyData.familyWords ⟨adj,s.data.cut⟩ s.data.remaining (4*s.data.scale) L.bits EN E

def Stored (heap : NaturalHeap) (root : ℕ) (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (words : List (List Bits)) (scale : Bits) : Prop :=
  CacheAt heap root s.data (cacheOf positive E s).optimal (cacheOf positive E s).candidate words (candidateWords EN E s) scale

theorem stored_extend {heap : NaturalHeap} {root : ℕ} {s : Code (Graph adj) demands L} {positive : 0<L}
    {EN : ResidualSearch.Enumeration (Node n L)} {E : ResidualSearch.Enumeration (Network n L)}
    {words : List (List Bits)} {scale : Bits} (stored : Stored heap root s positive EN E words scale) (ext : NaturalHeap) :
    Stored (heap++ext) root s positive EN E words scale := AdaptiveControllerStorage.cache_extend stored ext

theorem kept {d : Data n} {optimum : ℕ} {R M : Bits} {p : Pair n}
    (h : EpochScanHeadProgram.keep d optimum R M p=true) : flag d.remaining p=true := by
  simp only [EpochScanHeadProgram.keep,Bool.and_eq_true] at h
  exact h.2

noncomputable def scan (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R M : Bits)
    (cells : Pair n → Fin L) : List (Pair n) → Code (Graph adj) demands L → Code (Graph adj) demands L
  | [], s => s
  | p::ps, s =>
    if h : EpochScanHeadProgram.keep s.data (cacheOf positive E s).optimal R M p=true then
      scan positive E R M cells ps (sampleRound positive (cutOracle adj positive) s p (membership_of_flag s p (kept h)) (cells p))
    else s

theorem keep_spec (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R M : Bits)
    (s : Code (Graph adj) demands L) (p : Pair n) :
    EpochScanHeadProgram.keep s.data (cacheOf positive E s).optimal R M p=true ↔
      IntegerAdaptiveExecution.active (value R) (value M) (cacheOf positive E s)=true ∧ flag s.data.remaining p=true := by
  simp [EpochScanHeadProgram.keep,EpochScanHeadProgram.active,IntegerAdaptiveExecution.active,RetainedGridState.Cache.ready,
    Nat.ble_eq]
  intro _ _ _
  exact ⟨fun h => decide_eq_true h,fun h => of_decide_eq_true h⟩

theorem scan_exact (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R M : Bits)
    (cells : Pair n→Fin L) (order : List (Pair n)) (s : Code (Graph adj) demands L) :
    (IntegerAdaptiveExecution.scan (optimizer (adj:=adj) (demands:=demands) positive E) positive (cutOracle adj positive)
      (value R) (value M) cells order (cacheOf positive E s)).cache=
      cacheOf positive E (scan positive E R M cells order s) := by
  induction order generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [IntegerAdaptiveExecution.scan,scan]
    have condition : (IntegerAdaptiveExecution.active (value R) (value M) (cacheOf positive E s)=true ∧
        flag (cacheOf positive E s).state.data.remaining p=true) ↔
        EpochScanHeadProgram.keep s.data (cacheOf positive E s).optimal R M p=true := (keep_spec positive E R M s p).symm
    by_cases keep : EpochScanHeadProgram.keep s.data (cacheOf positive E s).optimal R M p=true
    · rw [dite_eq_left keep,dite_eq_left (condition.mpr keep)]
      exact ih _
    · rw [dite_eq_right keep,dite_eq_right (fun h => keep (condition.mp h))]

end DirectedFlowCutGap.EpochScanData
