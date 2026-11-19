import DirectedFlowCutGap.AdaptiveControllerProgram

/-! Uniform storage growth and affine-in-heap instruction budgets for each controller cycle. -/

namespace DirectedFlowCutGap.AdaptiveControllerBounds

open BinaryArithmetic EpochScanBounds

structure Limits where
  vertices : ℕ
  grid : ℕ
  trials : ℕ
  restarts : ℕ
  word : ℕ
  weights : ℕ
  scale : ℕ
  ratio : ℕ
  readyThreshold : ℕ

def Limits.threshold (b : Limits) : ℕ := currentWidth b.vertices b.weights

def Limits.stabilizeCells (b : Limits) : ℕ :=
  CacheStabilizeProgram.allocationBound b.vertices b.grid b.restarts b.weights b.scale b.ratio b.readyThreshold

def Limits.stabilizeInstructions (b : Limits) (H : ℕ) : ℕ :=
  CacheStabilizeProgram.instructionBound b.vertices b.grid b.restarts H b.weights b.scale b.ratio b.readyThreshold

def Limits.epochCells (b : Limits) : ℕ :=
  PhysicalEpochScanProgram.allocationBound b.vertices b.grid b.trials b.word b.weights b.scale b.ratio b.threshold

def Limits.epochInstructions (b : Limits) (H : ℕ) : ℕ :=
  PhysicalEpochScanProgram.instructionBound b.vertices b.grid b.trials H b.word b.weights b.scale b.ratio b.threshold

def Limits.stepCells (b : Limits) : ℕ := b.stabilizeCells+b.threshold+5+b.epochCells

def Limits.stepInstructions (b : Limits) (H : ℕ) : ℕ :=
  b.stabilizeInstructions H+ControllerEpochParameters.instructionBound (H+b.stabilizeCells)+
    b.epochInstructions (H+b.stabilizeCells+b.threshold+4)+26

def Limits.slope (b : Limits) : ℕ := 16*b.restarts+12+16*(b.vertices*b.vertices)

def loopLimit (b : Limits) (count H : ℕ) : ℕ :=
  count*(b.slope*(H+count*b.stepCells)+b.stepInstructions 0)+2

def instructionBound (b : Limits) (epochCount H : ℕ) : ℕ := loopLimit b (epochCount+1) H+1

theorem step_affine (b : Limits) (H : ℕ) : b.stepInstructions H=b.slope*H+b.stepInstructions 0 := by
  unfold Limits.stepInstructions Limits.slope Limits.stabilizeInstructions Limits.epochInstructions
    CacheStabilizeProgram.instructionBound PhysicalEpochScanProgram.instructionBound ControllerEpochParameters.instructionBound
    EpochScanBounds.loopBound
  dsimp only
  ring

theorem loop_advance (b : Limits) (count H H' head tail : ℕ) (grow : H'≤H+b.stepCells)
    (take : head≤ b.stepInstructions H) (rest : tail≤ loopLimit b count H') :
    head+tail ≤ loopLimit b (count+1) H := by
  let A := b.stepCells
  let base := b.stepInstructions 0
  let Q := b.slope*(H+(count+1)*A)+base
  have sz : H'+count*A≤H+(count+1)*A := by rw [Nat.succ_mul]; omega
  have ht : head≤Q := by
    rw [step_affine] at take
    refine take.trans ?_
    dsimp only [Q,base]
    gcongr
    exact Nat.le_add_right _ _
  have rt : tail≤count*Q+2 := rest.trans (by unfold loopLimit Q A base; gcongr)
  change head+tail≤(count+1)*Q+2
  rw [Nat.succ_mul]
  omega

theorem loop_stop (b : Limits) (count H head : ℕ) (take : head≤ b.stepInstructions H) :
    head ≤ loopLimit b (count+1) H := by
  have h := loop_advance b count H H head 0 (Nat.le_add_right _ _) take (Nat.zero_le _)
  simpa only [Nat.add_zero] using h

theorem prep_instructions_mono {H K : ℕ} (h : H≤K) :
    ControllerEpochParameters.instructionBound H ≤ ControllerEpochParameters.instructionBound K := by
  unfold ControllerEpochParameters.instructionBound
  gcongr

private theorem refresh_mono (n L : ℕ) {a b : ℕ} (h : a≤b) :
    CandidateRefreshProgram.instructionBound n L n.size L.size a ≤
      CandidateRefreshProgram.instructionBound n L n.size L.size b := by
  unfold CandidateRefreshProgram.instructionBound CandidateFamilyProgram.instructionBound
    CandidateFamilyScanProgram.instructionBound CandidateFamilyScanProgram.rowLimit CandidateDemandRowProgram.instructionBound
    CandidateRawSolverProgram.instructionBound CandidateCapacityMatrixProgram.instructionBound
    CandidateCapacitySetupProgram.instructionBound CandidateCapacityTableProgram.instructionBound
    CandidateCapacityTableProgram.tableBound CandidateCapacityTableProgram.rowBound CandidateCapacityCellProgram.instructionBound
    CandidateDescriptorCapacityProgram.instructionBound CandidateCoreCapacityProgram.instructionBound
  gcongr

private theorem round_mono (n L W B : ℕ) {a b : ℕ} (h : a≤b) :
    roundBound n L (n*n) W B a ≤ roundBound n L (n*n) W B b := by
  have proof := refresh_mono n L h
  unfold roundBound AdaptiveRoundRefreshProgram.instructionBound
  omega

private theorem cells_mono (n L W B R : ℕ) {a b M M' : ℕ} (scale : a≤b) (threshold : M≤M') :
    EpochScanBounds.stepCells n L (n*n) W B a R M ≤ EpochScanBounds.stepCells n L (n*n) W B b R M' := by
  have rounds := round_mono n L W B scale
  unfold EpochScanBounds.stepCells EpochScanHeadProgram.allocationBound CacheGatesProgram.allocationBound
    AdaptiveGatesProgram.instructionBound BinaryProductOrderProgram.instructionBound
  gcongr

private theorem base_mono (n L W B R : ℕ) {a b M M' : ℕ} (scale : a≤b) (threshold : M≤M') :
    EpochScanBounds.baseInstructions n L (n*n) W B a R M ≤ EpochScanBounds.baseInstructions n L (n*n) W B b R M' := by
  have rounds := round_mono n L W B scale
  unfold EpochScanBounds.baseInstructions EpochScanHeadProgram.instructionBound CacheGatesProgram.instructionBound
    AdaptiveGatesProgram.instructionBound BinaryProductOrderProgram.instructionBound
  gcongr

theorem epoch_bounds (b : Limits) {H H' scale threshold : ℕ} (heap : H≤H') (sc : scale≤b.scale) (th : threshold≤b.threshold) :
    PhysicalEpochScanProgram.instructionBound b.vertices b.grid b.trials H b.word b.weights scale b.ratio threshold ≤
      b.epochInstructions H' ∧
    PhysicalEpochScanProgram.allocationBound b.vertices b.grid b.trials b.word b.weights scale b.ratio threshold ≤ b.epochCells := by
  have cells := cells_mono b.vertices b.grid b.word b.weights b.ratio sc th
  have base := base_mono b.vertices b.grid b.word b.weights b.ratio sc th
  unfold Limits.epochInstructions Limits.epochCells PhysicalEpochScanProgram.instructionBound PhysicalEpochScanProgram.allocationBound
    EpochScanBounds.loopBound
  dsimp only
  constructor <;> gcongr

end DirectedFlowCutGap.AdaptiveControllerBounds
