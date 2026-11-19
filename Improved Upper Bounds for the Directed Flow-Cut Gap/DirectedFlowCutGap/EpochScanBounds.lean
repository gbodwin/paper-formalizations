import DirectedFlowCutGap.EpochScanData

/-! Uniform instruction and storage bounds for an epoch scan. -/

namespace DirectedFlowCutGap.EpochScanBounds

open BinaryArithmetic ImmutableReferenceSimulation RetainedGridState IntegralNetworkFlow
open EpochScanData (Graph Stored cacheOf candidateWords)
open CandidateEnumeration (Node Network)

def currentWidth (n B : ℕ) : ℕ := B+n+n*n
def optimumWidth (n L : ℕ) : ℕ := currentWidth n (max L.size (L+1).size)

def roundBound (n L cells W B scale : ℕ) : ℕ :=
  AdaptiveRoundRefreshProgram.instructionBound n L cells W n.size B scale

def stepCells (n L cells W B scale ratio threshold : ℕ) : ℕ :=
  EpochScanHeadProgram.allocationBound n (currentWidth n B) (optimumWidth n L) ratio threshold+
    roundBound n L cells W B scale

def baseInstructions (n L cells W B scale ratio threshold : ℕ) : ℕ :=
  EpochScanHeadProgram.instructionBound n 0 (currentWidth n B) (optimumWidth n L) ratio threshold+
    roundBound n L cells W B scale+10

def loopBound (count H A base : ℕ) : ℕ := count*(16*(H+count*A)+base)+2

theorem round_bound {n : ℕ} (p : Pair n) (L cells W B scale : ℕ) :
    AdaptiveRoundRefreshProgram.instructionBound n L cells W p.1.val.bits.length B scale ≤ roundBound n L cells W B scale := by
  have label : p.1.val.bits.length≤n.size := (Nat.size_eq_bits_len p.1.val).trans_le (Nat.size_le_size p.1.isLt.le)
  unfold roundBound AdaptiveRoundRefreshProgram.instructionBound EpochSelectedRoundProgram.instructionBound
    PhysicalSampledRoundProgram.instructionBound IntegerLevelCutProgram.instructionBound IntegerLevelVertexProgram.instructionBound
    GraphRecoveryController.instructionBound GraphDiscoveryProgram.discoveryBudget GraphDiscoveryProgram.roundBudget
    GraphDiscoveryProgram.passBudget GraphRelaxationProgram.instructionBound
  gcongr

theorem mass_widths {n L B : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}
    {positive : 0<L} {EN : ResidualSearch.Enumeration (Node n L)} {E : ResidualSearch.Enumeration (Network n L)}
    {s : Code (Graph adj) demands L} {words : List (List Bits)} {scale : Bits}
    (stored : Stored heap root s positive EN E words scale) (widths : ∀ ws∈words,∀ w∈ws,w.length≤B) :
    s.data.current.size≤currentWidth n B ∧ (cacheOf positive E s).optimal.size≤optimumWidth n L := by
  obtain ⟨live,best,atRoot,state,output⟩ := stored
  obtain ⟨packed,runtime,ctx,si,weights,free,atState,maskMass,atRuntime,atContext,table,flag,scaleRep,scaleValue,rows⟩ := state
  obtain ⟨table,mass,bits,pair,saved,data,massRep,massValue⟩ := output
  constructor
  · rw [s.valid.current_eq]
    exact ControllerWordWidth.mass_size s.data.weights s.data.remaining s.data.cut words rows widths
  · have width := CandidateFamilyData.family_width (L:=L) ⟨adj,s.data.cut⟩ s.data.remaining (4*s.data.scale) L.bits EN E
    rw [Nat.size_eq_bits_len] at width
    exact ControllerWordWidth.mass_size (cacheOf positive E s).candidate s.data.remaining s.data.cut
      (candidateWords EN E s) data width

theorem allocation_mono (n ratio threshold : ℕ) {cur cur' opt opt' : ℕ} (hc : cur≤cur') (ho : opt≤opt') :
    EpochScanHeadProgram.allocationBound n cur opt ratio threshold ≤ EpochScanHeadProgram.allocationBound n cur' opt' ratio threshold := by
  unfold EpochScanHeadProgram.allocationBound CacheGatesProgram.allocationBound AdaptiveGatesProgram.instructionBound
    BinaryProductOrderProgram.instructionBound
  gcongr

theorem instructions_mono (n H ratio threshold : ℕ) {cur cur' opt opt' : ℕ} (hc : cur≤cur') (ho : opt≤opt') :
    EpochScanHeadProgram.instructionBound n H cur opt ratio threshold ≤
      EpochScanHeadProgram.instructionBound n H cur' opt' ratio threshold := by
  unfold EpochScanHeadProgram.instructionBound CacheGatesProgram.instructionBound AdaptiveGatesProgram.instructionBound
    BinaryProductOrderProgram.instructionBound
  gcongr

theorem loop_extend (m H H' A base a b : ℕ) (heap : H'≤H+A) (head : a≤16*H+base)
    (tail : b≤loopBound m H' A base) : a+b ≤ loopBound (m+1) H A base := by
  let Q := 16*(H+(m+1)*A)+base
  have address : H'+m*A≤H+(m+1)*A := by rw [Nat.succ_mul]; omega
  have head' : a≤Q := by dsimp [Q]; omega
  have tail' : b ≤ m*Q+2 := tail.trans (by unfold loopBound Q; gcongr)
  change a+b≤(m+1)*Q+2
  rw [Nat.succ_mul]
  omega

theorem loop_stop (m H A base a : ℕ) (head : a≤16*H+base) : a ≤ loopBound (m+1) H A base := by
  have after := loop_extend m H H A base a 2 (Nat.le_add_right _ _) head (by unfold loopBound; omega)
  omega

end DirectedFlowCutGap.EpochScanBounds
