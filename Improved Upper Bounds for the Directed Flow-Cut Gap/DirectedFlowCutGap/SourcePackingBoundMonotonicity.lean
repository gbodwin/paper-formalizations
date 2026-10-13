import DirectedFlowCutGap.ActualSourcePacking

/-! Small compositional monotonicity lemmas for the existing nonnegative
input-cost formulas. No program or bound definition is changed. -/
namespace DirectedFlowCutGap.SourcePackingBound

@[gcongr] theorem mono_RowVertices_instructionBound {n n' : ℕ} (h0 : n ≤ n') :
    RowVertices.instructionBound n ≤ RowVertices.instructionBound n' := by
  dsimp only [RowVertices.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingParameters_instructionBound {n n' : ℕ} (h0 : n ≤ n') :
    PackingParameters.instructionBound n ≤ PackingParameters.instructionBound n' := by
  dsimp only [PackingParameters.instructionBound]
  gcongr

@[gcongr] theorem mono_ScalarQuotientRow_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    ScalarQuotientRow.instructionBound n B ≤ ScalarQuotientRow.instructionBound n' B' := by
  dsimp only [ScalarQuotientRow.instructionBound]
  gcongr

@[gcongr] theorem mono_GraphRelaxationProgram_perEntryBound {B B' N N' S S' : ℕ} (h0 : B ≤ B') (h1 : N ≤ N') (h2 : S ≤ S') :
    GraphRelaxationProgram.perEntryBound B N S ≤ GraphRelaxationProgram.perEntryBound B' N' S' := by
  dsimp only [GraphRelaxationProgram.perEntryBound]
  gcongr

@[gcongr] theorem mono_GraphRelaxationProgram_instructionBound {m m' B B' N N' S S' : ℕ} (h0 : m ≤ m') (h1 : B ≤ B') (h2 : N ≤ N') (h3 : S ≤ S') :
    GraphRelaxationProgram.instructionBound m B N S ≤ GraphRelaxationProgram.instructionBound m' B' N' S' := by
  dsimp only [GraphRelaxationProgram.instructionBound]
  gcongr

@[gcongr] theorem mono_GraphDiscoveryProgram_passBudget {m m' M M' W W' N N' S S' : ℕ} (h0 : m ≤ m') (h1 : M ≤ M') (h2 : W ≤ W') (h3 : N ≤ N') (h4 : S ≤ S') :
    GraphDiscoveryProgram.passBudget m M W N S ≤ GraphDiscoveryProgram.passBudget m' M' W' N' S' := by
  dsimp only [GraphDiscoveryProgram.passBudget]
  gcongr

@[gcongr] theorem mono_GraphDiscoveryProgram_roundBudget {m m' k k' W W' N N' S S' : ℕ} (h0 : m ≤ m') (h1 : k ≤ k') (h2 : W ≤ W') (h3 : N ≤ N') (h4 : S ≤ S') :
    GraphDiscoveryProgram.roundBudget m k W N S ≤ GraphDiscoveryProgram.roundBudget m' k' W' N' S' := by
  dsimp only [GraphDiscoveryProgram.roundBudget]
  gcongr

@[gcongr] theorem mono_GraphDiscoveryProgram_roundWidth {B B' k k' : ℕ} (h0 : B ≤ B') (h1 : k ≤ k') :
    GraphDiscoveryProgram.roundWidth B k ≤ GraphDiscoveryProgram.roundWidth B' k' := by
  dsimp only [GraphDiscoveryProgram.roundWidth]
  gcongr

@[gcongr] theorem mono_GraphDiscoveryProgram_discoveryWidth {m m' B B' : ℕ} (h0 : m ≤ m') (h1 : B ≤ B') :
    GraphDiscoveryProgram.discoveryWidth m B ≤ GraphDiscoveryProgram.discoveryWidth m' B' := by
  dsimp only [GraphDiscoveryProgram.discoveryWidth]
  gcongr

@[gcongr] theorem mono_GraphDiscoveryProgram_lookupBudget {m m' W W' : ℕ} (h0 : m ≤ m') (h1 : W ≤ W') :
    GraphDiscoveryProgram.lookupBudget m W ≤ GraphDiscoveryProgram.lookupBudget m' W' := by
  dsimp only [GraphDiscoveryProgram.lookupBudget]
  gcongr

@[gcongr] theorem mono_GraphDiscoveryProgram_discoveryBudget {m m' B B' N N' S S' : ℕ} (h0 : m ≤ m') (h1 : B ≤ B') (h2 : N ≤ N') (h3 : S ≤ S') :
    GraphDiscoveryProgram.discoveryBudget m B N S ≤ GraphDiscoveryProgram.discoveryBudget m' B' N' S' := by
  dsimp only [GraphDiscoveryProgram.discoveryBudget]
  gcongr

@[gcongr] theorem mono_SupportRecoveryProgram_scanCap {S S' W W' N N' : ℕ} (h0 : S ≤ S') (h1 : W ≤ W') (h2 : N ≤ N') :
    SupportRecoveryProgram.scanCap S W N ≤ SupportRecoveryProgram.scanCap S' W' N' := by
  dsimp only [SupportRecoveryProgram.scanCap]
  gcongr

@[gcongr] theorem mono_SupportRecoveryProgram_searchCap {V V' S S' W W' N N' : ℕ} (h0 : V ≤ V') (h1 : S ≤ S') (h2 : W ≤ W') (h3 : N ≤ N') :
    SupportRecoveryProgram.searchCap V S W N ≤ SupportRecoveryProgram.searchCap V' S' W' N' := by
  dsimp only [SupportRecoveryProgram.searchCap]
  gcongr

@[gcongr] theorem mono_CanonicalRationalSum_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    CanonicalRationalSum.instructionBound n B ≤ CanonicalRationalSum.instructionBound n' B' := by
  dsimp only [CanonicalRationalSum.instructionBound]
  gcongr

@[gcongr] theorem mono_MaterializedPathSum_instructionBound {m m' B B' N N' sourceLength sourceLength' : ℕ} (h0 : m ≤ m') (h1 : B ≤ B') (h2 : N ≤ N') (h3 : sourceLength ≤ sourceLength') :
    MaterializedPathSum.instructionBound m B N sourceLength ≤ MaterializedPathSum.instructionBound m' B' N' sourceLength' := by
  dsimp only [MaterializedPathSum.instructionBound]
  gcongr

@[gcongr] theorem mono_CostedSupportProgram_recoveryCap {N N' S S' W W' : ℕ} (h0 : N ≤ N') (h1 : S ≤ S') (h2 : W ≤ W') :
    CostedSupportProgram.recoveryCap N S W ≤ CostedSupportProgram.recoveryCap N' S' W' := by
  dsimp only [CostedSupportProgram.recoveryCap]
  gcongr

@[gcongr] theorem mono_GraphRecoveryController_instructionBound {N N' W W' S S' : ℕ} (h0 : N ≤ N') (h1 : W ≤ W') (h2 : S ≤ S') :
    GraphRecoveryController.instructionBound N W S ≤ GraphRecoveryController.instructionBound N' W' S' := by
  dsimp only [GraphRecoveryController.instructionBound]
  gcongr

@[gcongr] theorem mono_DemandCollection_instructionBound {k k' n n' W W' : ℕ} (h0 : k ≤ k') (h1 : n ≤ n') (h2 : W ≤ W') :
    DemandCollection.instructionBound k n W ≤ DemandCollection.instructionBound k' n' W' := by
  dsimp only [DemandCollection.instructionBound]
  gcongr

@[gcongr] theorem mono_OracleMask_instructionBound {vertices vertices' edges edges' W W' : ℕ} (h0 : vertices ≤ vertices') (h1 : edges ≤ edges') (h2 : W ≤ W') :
    OracleMask.instructionBound vertices edges W ≤ OracleMask.instructionBound vertices' edges' W' := by
  dsimp only [OracleMask.instructionBound]
  gcongr

@[gcongr] theorem mono_CapacityBottleneck_instructionBound {n n' W W' : ℕ} (h0 : n ≤ n') (h1 : W ≤ W') :
    CapacityBottleneck.instructionBound n W ≤ CapacityBottleneck.instructionBound n' W' := by
  dsimp only [CapacityBottleneck.instructionBound]
  gcongr

@[gcongr] theorem mono_GraphOracleMachine_instructionBound {demands demands' n n' W W' : ℕ} (h0 : demands ≤ demands') (h1 : n ≤ n') (h2 : W ≤ W') :
    GraphOracleMachine.instructionBound demands n W ≤ GraphOracleMachine.instructionBound demands' n' W' := by
  dsimp only [GraphOracleMachine.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingStart_initialWidth {B B' : ℕ} (h0 : B ≤ B') :
    PackingStart.initialWidth B ≤ PackingStart.initialWidth B' := by
  dsimp only [PackingStart.initialWidth]
  gcongr

@[gcongr] theorem mono_NormalizedRow_scalarWidth {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    NormalizedRow.scalarWidth n B ≤ NormalizedRow.scalarWidth n' B' := by
  dsimp only [NormalizedRow.scalarWidth]
  gcongr

@[gcongr] theorem mono_NormalizedRow_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    NormalizedRow.instructionBound n B ≤ NormalizedRow.instructionBound n' B' := by
  dsimp only [NormalizedRow.instructionBound]
  gcongr

@[gcongr] theorem mono_ObjectiveProductList_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    ObjectiveProductList.instructionBound n B ≤ ObjectiveProductList.instructionBound n' B' := by
  dsimp only [ObjectiveProductList.instructionBound]
  gcongr

@[gcongr] theorem mono_ObjectiveRow_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    ObjectiveRow.instructionBound n B ≤ ObjectiveRow.instructionBound n' B' := by
  dsimp only [ObjectiveRow.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingStart_bestWidth {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingStart.bestWidth n B ≤ PackingStart.bestWidth n' B' := by
  dsimp only [PackingStart.bestWidth]
  gcongr

@[gcongr] theorem mono_PackingStart_instructionBound {d d' n n' B B' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') :
    PackingStart.instructionBound d n B ≤ PackingStart.instructionBound d' n' B' := by
  dsimp only [PackingStart.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingGuard_objectiveWidth {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingGuard.objectiveWidth n B ≤ PackingGuard.objectiveWidth n' B' := by
  dsimp only [PackingGuard.objectiveWidth]
  gcongr

@[gcongr] theorem mono_PackingGuard_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingGuard.instructionBound n B ≤ PackingGuard.instructionBound n' B' := by
  dsimp only [PackingGuard.instructionBound]
  gcongr

@[gcongr] theorem mono_AdaptivePackingState_normalizedWidth {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    AdaptivePackingState.normalizedWidth n B ≤ AdaptivePackingState.normalizedWidth n' B' := by
  dsimp only [AdaptivePackingState.normalizedWidth]
  gcongr

@[gcongr] theorem mono_PackingEntry_instructionBound {B B' : ℕ} (h0 : B ≤ B') :
    PackingEntry.instructionBound B ≤ PackingEntry.instructionBound B' := by
  dsimp only [PackingEntry.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingUpdateRow_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingUpdateRow.instructionBound n B ≤ PackingUpdateRow.instructionBound n' B' := by
  dsimp only [PackingUpdateRow.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingLoadRow_entryBound {B B' : ℕ} (h0 : B ≤ B') :
    PackingLoadRow.entryBound B ≤ PackingLoadRow.entryBound B' := by
  dsimp only [PackingLoadRow.entryBound]
  gcongr

@[gcongr] theorem mono_PackingLoadRow_instructionBound {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingLoadRow.instructionBound n B ≤ PackingLoadRow.instructionBound n' B' := by
  dsimp only [PackingLoadRow.instructionBound]
  gcongr

@[gcongr] theorem mono_AdaptivePackingState_instructionBound {d d' n n' B B' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') :
    AdaptivePackingState.instructionBound d n B ≤ AdaptivePackingState.instructionBound d' n' B' := by
  dsimp only [AdaptivePackingState.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingIteration_smallWidth {B B' t t' : ℕ} (h0 : B ≤ B') (h1 : t ≤ t') :
    PackingIteration.smallWidth B t ≤ PackingIteration.smallWidth B' t' := by
  dsimp only [PackingIteration.smallWidth]
  gcongr

@[gcongr] theorem mono_PackingIteration_commonWidth {n n' B B' t t' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') (h2 : t ≤ t') :
    PackingIteration.commonWidth n B t ≤ PackingIteration.commonWidth n' B' t' := by
  dsimp only [PackingIteration.commonWidth]
  gcongr

@[gcongr] theorem mono_PackingIteration_instructionBound {d d' n n' B B' fuel fuel' bits bits' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') (h3 : fuel ≤ fuel') (h4 : bits ≤ bits') :
    PackingIteration.instructionBound d n B fuel bits ≤ PackingIteration.instructionBound d' n' B' fuel' bits' := by
  dsimp only [PackingIteration.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingRun_startWidth {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingRun.startWidth n B ≤ PackingRun.startWidth n' B' := by
  dsimp only [PackingRun.startWidth]
  gcongr

@[gcongr] theorem mono_PackingRun_instructionBound {d d' n n' B B' fuel fuel' bits bits' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') (h3 : fuel ≤ fuel') (h4 : bits ≤ bits') :
    PackingRun.instructionBound d n B fuel bits ≤ PackingRun.instructionBound d' n' B' fuel' bits' := by
  dsimp only [PackingRun.instructionBound]
  gcongr

@[gcongr] theorem mono_PackingComplete_parameterWidth {n n' B B' : ℕ} (h0 : n ≤ n') (h1 : B ≤ B') :
    PackingComplete.parameterWidth n B ≤ PackingComplete.parameterWidth n' B' := by
  dsimp only [PackingComplete.parameterWidth]
  gcongr

@[gcongr] theorem mono_PackingComplete_instructionBound {d d' n n' B B' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') :
    PackingComplete.instructionBound d n B ≤ PackingComplete.instructionBound d' n' B' := by
  dsimp only [PackingComplete.instructionBound]
  gcongr

@[gcongr] theorem mono_PreparedPacking_instructionBound {d d' n n' B B' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') :
    PreparedPacking.instructionBound d n B ≤ PreparedPacking.instructionBound d' n' B' := by
  dsimp only [PreparedPacking.instructionBound]
  gcongr

@[gcongr] theorem mono_EnumeratedPacking_instructionBound {d d' n n' B B' : ℕ} (h0 : d ≤ d') (h1 : n ≤ n') (h2 : B ≤ B') :
    EnumeratedPacking.instructionBound d n B ≤ EnumeratedPacking.instructionBound d' n' B' := by
  dsimp only [EnumeratedPacking.instructionBound]
  gcongr

end DirectedFlowCutGap.SourcePackingBound
