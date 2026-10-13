import DirectedFlowCutGap.GridFamilyEnvelope
import DirectedFlowCutGap.ActualGridFamilyInput
import DirectedFlowCutGap.GridFamilyInputCallLift
import DirectedFlowCutGap.GridFamilyInputCalls
import DirectedFlowCutGap.GridFamilyInputOriginal
import DirectedFlowCutGap.GridFamilyInputPrefix
import DirectedFlowCutGap.GridFamilyInputPrepare
import DirectedFlowCutGap.GridFamilyInputProgram
import DirectedFlowCutGap.GridFamilyInputTrace
import DirectedFlowCutGap.ActualGridFamily
import DirectedFlowCutGap.GridFamilyAdvance
import DirectedFlowCutGap.GridFamilyCallLift
import DirectedFlowCutGap.GridFamilyControlCalls
import DirectedFlowCutGap.GridFamilyData
import DirectedFlowCutGap.GridFamilyExecution
import DirectedFlowCutGap.GridFamilyGuard
import DirectedFlowCutGap.GridFamilyGuessCall
import DirectedFlowCutGap.GridFamilyHead
import DirectedFlowCutGap.GridFamilyOriginal
import DirectedFlowCutGap.GridFamilyPrimitiveCalls
import DirectedFlowCutGap.GridFamilyProgram
import DirectedFlowCutGap.GridFamilySpecification
import DirectedFlowCutGap.GridFamilyTrace
import DirectedFlowCutGap.ActualMinimumGuess
import DirectedFlowCutGap.MinimumGuessCallLift
import DirectedFlowCutGap.MinimumGuessCalls
import DirectedFlowCutGap.MinimumGuessExecution
import DirectedFlowCutGap.MinimumGuessPreparation
import DirectedFlowCutGap.MinimumGuessProgram
import DirectedFlowCutGap.MinimumGuessRange
import DirectedFlowCutGap.MinimumGuessTrace
import DirectedFlowCutGap.MinimumGuessWidth
import DirectedFlowCutGap.ActualOriginalRowMinimum
import DirectedFlowCutGap.OriginalRowMinimumCallLift
import DirectedFlowCutGap.OriginalRowMinimumCalls
import DirectedFlowCutGap.OriginalRowMinimumExecution
import DirectedFlowCutGap.OriginalRowMinimumIndex
import DirectedFlowCutGap.OriginalRowMinimumProgram
import DirectedFlowCutGap.OriginalRowMinimumTrace
import DirectedFlowCutGap.ActualMinimumShift
import DirectedFlowCutGap.MinimumShiftBound
import DirectedFlowCutGap.MinimumShiftCallLift
import DirectedFlowCutGap.MinimumShiftCalls
import DirectedFlowCutGap.MinimumShiftExecution
import DirectedFlowCutGap.MinimumShiftProgram
import DirectedFlowCutGap.MinimumShiftRange
import DirectedFlowCutGap.MinimumShiftTrace
import DirectedFlowCutGap.ActualScalarAdditionRow
import DirectedFlowCutGap.ScalarAdditionRowBounds
import DirectedFlowCutGap.ScalarAdditionRowCall
import DirectedFlowCutGap.ScalarAdditionRowEncoding
import DirectedFlowCutGap.ScalarAdditionRowProgram
import DirectedFlowCutGap.ScalarAdditionRowRefinement
import DirectedFlowCutGap.ScalarAdditionRowTrace
import DirectedFlowCutGap.ActualShiftedGrid
import DirectedFlowCutGap.ShiftedGridBound
import DirectedFlowCutGap.ShiftedGridCallLift
import DirectedFlowCutGap.ShiftedGridCalls
import DirectedFlowCutGap.ShiftedGridExecution
import DirectedFlowCutGap.ShiftedGridProgram
import DirectedFlowCutGap.ShiftedGridRange
import DirectedFlowCutGap.ShiftedGridTrace
import DirectedFlowCutGap.ActualLambdaRow
import DirectedFlowCutGap.LambdaRowBound
import DirectedFlowCutGap.LambdaRowCallLift
import DirectedFlowCutGap.LambdaRowCalls
import DirectedFlowCutGap.LambdaRowExecution
import DirectedFlowCutGap.LambdaRowPrefix
import DirectedFlowCutGap.LambdaRowProgram
import DirectedFlowCutGap.LambdaRowTrace
import DirectedFlowCutGap.ActualLambdaGrid
import DirectedFlowCutGap.LambdaGridBound
import DirectedFlowCutGap.LambdaGridCallLift
import DirectedFlowCutGap.LambdaGridCalls
import DirectedFlowCutGap.LambdaGridExecution
import DirectedFlowCutGap.LambdaGridProgram
import DirectedFlowCutGap.LambdaGridRangeBound
import DirectedFlowCutGap.LambdaGridTrace
import DirectedFlowCutGap.ActualNaturalFraction
import DirectedFlowCutGap.NaturalFractionExecution
import DirectedFlowCutGap.NaturalFractionProgram
import DirectedFlowCutGap.ActualLambdaCore
import DirectedFlowCutGap.LambdaCoreBound
import DirectedFlowCutGap.LambdaCoreCallLift
import DirectedFlowCutGap.LambdaCoreCalls
import DirectedFlowCutGap.LambdaCoreExecution
import DirectedFlowCutGap.LambdaCorePowerPrefix
import DirectedFlowCutGap.LambdaCorePrefix
import DirectedFlowCutGap.LambdaCoreProgram
import DirectedFlowCutGap.LambdaCoreTrace
import DirectedFlowCutGap.BinaryBorrowProgram
import DirectedFlowCutGap.ActualBinaryPredecessor
import DirectedFlowCutGap.BinaryPredecessorBound
import DirectedFlowCutGap.BinaryPredecessorCallLift
import DirectedFlowCutGap.BinaryPredecessorCalls
import DirectedFlowCutGap.BinaryPredecessorExecution
import DirectedFlowCutGap.BinaryPredecessorProgram
import DirectedFlowCutGap.BinaryPredecessorTrace
import DirectedFlowCutGap.ActualBinaryPower
import DirectedFlowCutGap.BinaryPowerBound
import DirectedFlowCutGap.BinaryPowerCallLift
import DirectedFlowCutGap.BinaryPowerCalls
import DirectedFlowCutGap.BinaryPowerExecution
import DirectedFlowCutGap.BinaryPowerFinish
import DirectedFlowCutGap.BinaryPowerProgram
import DirectedFlowCutGap.BinaryPowerTrace
import DirectedFlowCutGap.ActualGridFuel
import DirectedFlowCutGap.GridFuelBound
import DirectedFlowCutGap.GridFuelCallLift
import DirectedFlowCutGap.GridFuelCalls
import DirectedFlowCutGap.GridFuelConstants
import DirectedFlowCutGap.GridFuelExecution
import DirectedFlowCutGap.GridFuelProgram
import DirectedFlowCutGap.GridFuelTrace
import DirectedFlowCutGap.ActualGridInput
import DirectedFlowCutGap.GridInputBound
import DirectedFlowCutGap.GridInputCallLift
import DirectedFlowCutGap.GridInputCalls
import DirectedFlowCutGap.GridInputExecution
import DirectedFlowCutGap.GridInputProgram
import DirectedFlowCutGap.GridInputTrace
import DirectedFlowCutGap.OriginalGridInput
import DirectedFlowCutGap.ActualBinarySize
import DirectedFlowCutGap.BinarySizeCallLift
import DirectedFlowCutGap.BinarySizeCalls
import DirectedFlowCutGap.BinarySizeExecution
import DirectedFlowCutGap.BinarySizeProgram
import DirectedFlowCutGap.BinarySizeTrace
import DirectedFlowCutGap.BinarySizeValue
import DirectedFlowCutGap.ActualBinaryMaximum
import DirectedFlowCutGap.BinaryMaximumCallLift
import DirectedFlowCutGap.BinaryMaximumExecution
import DirectedFlowCutGap.BinaryMaximumProgram
import DirectedFlowCutGap.BinaryMaximumTrace
import DirectedFlowCutGap.ActualFractionWidth
import DirectedFlowCutGap.FractionWidthCallLift
import DirectedFlowCutGap.FractionWidthCalls
import DirectedFlowCutGap.FractionWidthExecution
import DirectedFlowCutGap.FractionWidthProgram
import DirectedFlowCutGap.FractionWidthTrace
import DirectedFlowCutGap.ActualInputWidth
import DirectedFlowCutGap.InputWidthBound
import DirectedFlowCutGap.InputWidthCallLift
import DirectedFlowCutGap.InputWidthCalls
import DirectedFlowCutGap.InputWidthExecution
import DirectedFlowCutGap.InputWidthProgram
import DirectedFlowCutGap.InputWidthTrace
import DirectedFlowCutGap.OriginalInputWidth
import DirectedFlowCutGap.BinaryFractionalGuesses
import DirectedFlowCutGap.ActualPositiveInventory
import DirectedFlowCutGap.PositiveInventoryBranches
import DirectedFlowCutGap.PositiveInventoryCall
import DirectedFlowCutGap.PositiveInventoryCallLift
import DirectedFlowCutGap.PositiveInventoryData
import DirectedFlowCutGap.PositiveInventoryExecution
import DirectedFlowCutGap.PositiveInventoryPrefix
import DirectedFlowCutGap.PositiveInventoryProgram
import DirectedFlowCutGap.PositiveInventoryRefinement
import DirectedFlowCutGap.PositiveInventoryTrace
import DirectedFlowCutGap.ActualPositiveMinimum
import DirectedFlowCutGap.OriginalMinimumPositive
import DirectedFlowCutGap.PositiveMinimumArgminCore
import DirectedFlowCutGap.PositiveMinimumBound
import DirectedFlowCutGap.PositiveMinimumCallLift
import DirectedFlowCutGap.PositiveMinimumCalls
import DirectedFlowCutGap.PositiveMinimumExecution
import DirectedFlowCutGap.PositiveMinimumProgram
import DirectedFlowCutGap.PositiveMinimumRefinement
import DirectedFlowCutGap.PositiveMinimumTrace
import DirectedFlowCutGap.PositiveMinimumValue
import DirectedFlowCutGap.ActualOriginalDispatch
import DirectedFlowCutGap.OriginalDispatchActive
import DirectedFlowCutGap.OriginalDispatchCallLift
import DirectedFlowCutGap.OriginalDispatchCalls
import DirectedFlowCutGap.OriginalDispatchExecution
import DirectedFlowCutGap.OriginalDispatchPrefix
import DirectedFlowCutGap.OriginalDispatchProgram
import DirectedFlowCutGap.OriginalDispatchSpec
import DirectedFlowCutGap.OriginalDispatchTag
import DirectedFlowCutGap.OriginalDispatchTrace
import DirectedFlowCutGap.ActualAvoidingDemandScan
import DirectedFlowCutGap.AvoidingDemandScanCall
import DirectedFlowCutGap.AvoidingDemandScanCallLift
import DirectedFlowCutGap.AvoidingDemandScanExecution
import DirectedFlowCutGap.AvoidingDemandScanHead
import DirectedFlowCutGap.AvoidingDemandScanProgram
import DirectedFlowCutGap.AvoidingDemandScanTrace
import DirectedFlowCutGap.ActualAvoidingZeroContext
import DirectedFlowCutGap.AvoidingGraphContextExecution
import DirectedFlowCutGap.AvoidingGraphContextProgram
import DirectedFlowCutGap.AvoidingGraphContextTrace
import DirectedFlowCutGap.AvoidingZeroContextCallLift
import DirectedFlowCutGap.AvoidingZeroContextCalls
import DirectedFlowCutGap.AvoidingZeroContextExecution
import DirectedFlowCutGap.AvoidingZeroContextProgram
import DirectedFlowCutGap.AvoidingZeroContextTrace
import DirectedFlowCutGap.ActualAvoidingShortest
import DirectedFlowCutGap.AvoidingShortestBounds
import DirectedFlowCutGap.AvoidingShortestCallLift
import DirectedFlowCutGap.AvoidingShortestCalls
import DirectedFlowCutGap.AvoidingShortestExecution
import DirectedFlowCutGap.AvoidingShortestOriginal
import DirectedFlowCutGap.AvoidingShortestProgram
import DirectedFlowCutGap.AvoidingShortestRefinement
import DirectedFlowCutGap.AvoidingShortestTrace
import DirectedFlowCutGap.BinaryWalkCostCongruence
import DirectedFlowCutGap.ActualAvoidingKeptPath
import DirectedFlowCutGap.AvoidingKeptPathCallLift
import DirectedFlowCutGap.AvoidingKeptPathCalls
import DirectedFlowCutGap.AvoidingKeptPathExecution
import DirectedFlowCutGap.AvoidingKeptPathProgram
import DirectedFlowCutGap.AvoidingKeptPathTrace
import DirectedFlowCutGap.ActualEmptyDemandEdge
import DirectedFlowCutGap.EmptyDemandEdgeCallLift
import DirectedFlowCutGap.EmptyDemandEdgeCalls
import DirectedFlowCutGap.EmptyDemandEdgeExecution
import DirectedFlowCutGap.EmptyDemandEdgeFinish
import DirectedFlowCutGap.EmptyDemandEdgeProgram
import DirectedFlowCutGap.EmptyDemandEdgeTrace
import DirectedFlowCutGap.ActualEmptyDemandScan
import DirectedFlowCutGap.EmptyDemandScanCall
import DirectedFlowCutGap.EmptyDemandScanCallLift
import DirectedFlowCutGap.EmptyDemandScanExecution
import DirectedFlowCutGap.EmptyDemandScanProgram
import DirectedFlowCutGap.EmptyDemandScanTrace
import DirectedFlowCutGap.ActualKeptAdjacencyRow
import DirectedFlowCutGap.KeptAdjacencyRowExecution
import DirectedFlowCutGap.KeptAdjacencyRowFlag
import DirectedFlowCutGap.KeptAdjacencyRowProgram
import DirectedFlowCutGap.KeptAdjacencyRowTrace
import DirectedFlowCutGap.ActualKeptAdjacencyMatrix
import DirectedFlowCutGap.KeptAdjacencyMatrixCall
import DirectedFlowCutGap.KeptAdjacencyMatrixCallLift
import DirectedFlowCutGap.KeptAdjacencyMatrixExecution
import DirectedFlowCutGap.KeptAdjacencyMatrixProgram
import DirectedFlowCutGap.KeptAdjacencyMatrixRepresentation
import DirectedFlowCutGap.KeptAdjacencyMatrixTrace
import DirectedFlowCutGap.ActualKeptAdjacencyInput
import DirectedFlowCutGap.KeptAdjacencyInputCallLift
import DirectedFlowCutGap.KeptAdjacencyInputCalls
import DirectedFlowCutGap.KeptAdjacencyInputExecution
import DirectedFlowCutGap.KeptAdjacencyInputProgram
import DirectedFlowCutGap.KeptAdjacencyInputTrace
import DirectedFlowCutGap.ActualKeptVertex
import DirectedFlowCutGap.KeptVertexComparison
import DirectedFlowCutGap.KeptVertexEndpoints
import DirectedFlowCutGap.KeptVertexExecution
import DirectedFlowCutGap.KeptVertexFinish
import DirectedFlowCutGap.KeptVertexProgram
import DirectedFlowCutGap.ActualKeptMask
import DirectedFlowCutGap.KeptMaskCall
import DirectedFlowCutGap.KeptMaskCallLift
import DirectedFlowCutGap.KeptMaskExecution
import DirectedFlowCutGap.KeptMaskProgram
import DirectedFlowCutGap.KeptMaskTrace
import DirectedFlowCutGap.ActualKeptMaskInput
import DirectedFlowCutGap.KeptMaskInputCallLift
import DirectedFlowCutGap.KeptMaskInputCalls
import DirectedFlowCutGap.KeptMaskInputExecution
import DirectedFlowCutGap.KeptMaskInputProgram
import DirectedFlowCutGap.KeptMaskInputTrace
import DirectedFlowCutGap.ActualPackingZeroMask
import DirectedFlowCutGap.PackingZeroMaskCall
import DirectedFlowCutGap.PackingZeroMaskCallLift
import DirectedFlowCutGap.PackingZeroMaskExecution
import DirectedFlowCutGap.PackingZeroMaskProgram
import DirectedFlowCutGap.PackingZeroMaskRefinement
import DirectedFlowCutGap.PackingZeroMaskTrace
import DirectedFlowCutGap.SourcePackingPolynomialBound
import DirectedFlowCutGap.SourcePackingPolynomialCosts
import DirectedFlowCutGap.SourcePackingPolynomialExecution
import DirectedFlowCutGap.ActualPackingSourceInput
import DirectedFlowCutGap.PackingSourceContracts
import DirectedFlowCutGap.PackingSourceInputCallLift
import DirectedFlowCutGap.PackingSourceInputCalls
import DirectedFlowCutGap.PackingSourceInputExecution
import DirectedFlowCutGap.PackingSourceInputProgram
import DirectedFlowCutGap.SourceMatrixExecution
import DirectedFlowCutGap.SourceMatrixProjection
import DirectedFlowCutGap.ActualSourcePacking
import DirectedFlowCutGap.SourcePackingBoundMonotonicity
import DirectedFlowCutGap.SourcePackingCallLift
import DirectedFlowCutGap.SourcePackingEncoding
import DirectedFlowCutGap.SourcePackingExecution
import DirectedFlowCutGap.SourcePackingInputLength
import DirectedFlowCutGap.SourcePackingLengthExecution
import DirectedFlowCutGap.SourcePackingProgram
import DirectedFlowCutGap.ActualEnumeratedPacking
import DirectedFlowCutGap.ActualRowVertices
import DirectedFlowCutGap.EnumeratedPackingCallLift
import DirectedFlowCutGap.EnumeratedPackingExecution
import DirectedFlowCutGap.EnumeratedPackingProgram
import DirectedFlowCutGap.RowVertexInitialization
import DirectedFlowCutGap.RowVertexScan
import DirectedFlowCutGap.RowVerticesCallLift
import DirectedFlowCutGap.RowVerticesExecution
import DirectedFlowCutGap.RowVerticesLabels
import DirectedFlowCutGap.RowVerticesProgram
import DirectedFlowCutGap.VertexListReverse
import DirectedFlowCutGap.ActualPreparedPacking
import DirectedFlowCutGap.PackingInputConstruction
import DirectedFlowCutGap.PreparedPackingCallLift
import DirectedFlowCutGap.PreparedPackingExecution
import DirectedFlowCutGap.PreparedPackingProgram
import DirectedFlowCutGap.ActualPackingParameters
import DirectedFlowCutGap.PackingDimension
import DirectedFlowCutGap.PackingParametersArithmeticCall
import DirectedFlowCutGap.PackingParametersBounds
import DirectedFlowCutGap.PackingParametersCallLift
import DirectedFlowCutGap.PackingParametersConstants
import DirectedFlowCutGap.PackingParametersDimensionCall
import DirectedFlowCutGap.PackingParametersExecution
import DirectedFlowCutGap.PackingParametersProgram
import DirectedFlowCutGap.PackingParametersQuotientCall
import DirectedFlowCutGap.PackingParametersSpecification
import DirectedFlowCutGap.ActualCompletePacking
import DirectedFlowCutGap.PackingCompleteCallLift
import DirectedFlowCutGap.PackingCompleteExecution
import DirectedFlowCutGap.PackingCompleteParametersCall
import DirectedFlowCutGap.PackingCompleteProgram
import DirectedFlowCutGap.PackingCompleteRunCall
import DirectedFlowCutGap.ActualPackingRun
import DirectedFlowCutGap.PackingRunCallLift
import DirectedFlowCutGap.PackingRunExecution
import DirectedFlowCutGap.PackingRunIterationCall
import DirectedFlowCutGap.PackingRunProgram
import DirectedFlowCutGap.PackingRunStartCall
import DirectedFlowCutGap.PackingRunStartWidth
import DirectedFlowCutGap.ActualPackingIteration
import DirectedFlowCutGap.PackingIterationAdvance
import DirectedFlowCutGap.PackingIterationBound
import DirectedFlowCutGap.PackingIterationCallLift
import DirectedFlowCutGap.PackingIterationCounterCall
import DirectedFlowCutGap.PackingIterationExecution
import DirectedFlowCutGap.PackingIterationFuel
import DirectedFlowCutGap.PackingIterationLoop
import DirectedFlowCutGap.PackingIterationLoopBound
import DirectedFlowCutGap.PackingIterationProgram
import DirectedFlowCutGap.PackingIterationSpecification
import DirectedFlowCutGap.PackingIterationStateSize
import DirectedFlowCutGap.PackingIterationStepCall
import DirectedFlowCutGap.PackingIterationWidth
import DirectedFlowCutGap.ActualAdaptivePackingStep
import DirectedFlowCutGap.ActualPackingAmount
import DirectedFlowCutGap.ActualPackingLoadRow
import DirectedFlowCutGap.AdaptivePackingActiveExecution
import DirectedFlowCutGap.AdaptivePackingActiveSelection
import DirectedFlowCutGap.AdaptivePackingActiveTail
import DirectedFlowCutGap.AdaptivePackingActualTotalLoads
import DirectedFlowCutGap.AdaptivePackingActualWeights
import DirectedFlowCutGap.AdaptivePackingAmountState
import DirectedFlowCutGap.AdaptivePackingArithmeticCalls
import DirectedFlowCutGap.AdaptivePackingBestState
import DirectedFlowCutGap.AdaptivePackingCallLift
import DirectedFlowCutGap.AdaptivePackingChoiceState
import DirectedFlowCutGap.AdaptivePackingContextState
import DirectedFlowCutGap.AdaptivePackingFieldPath
import DirectedFlowCutGap.AdaptivePackingGraphCalls
import DirectedFlowCutGap.AdaptivePackingGuardCall
import DirectedFlowCutGap.AdaptivePackingLoadOutput
import DirectedFlowCutGap.AdaptivePackingNormalizedState
import DirectedFlowCutGap.AdaptivePackingObjectiveState
import DirectedFlowCutGap.AdaptivePackingOracleState
import DirectedFlowCutGap.AdaptivePackingOriginalData
import DirectedFlowCutGap.AdaptivePackingScalarCalls
import DirectedFlowCutGap.AdaptivePackingSelectedData
import DirectedFlowCutGap.AdaptivePackingStateOutput
import DirectedFlowCutGap.AdaptivePackingStateProgram
import DirectedFlowCutGap.AdaptivePackingStepBounds
import DirectedFlowCutGap.AdaptivePackingStepExecution
import DirectedFlowCutGap.AdaptivePackingUpdateCalls
import DirectedFlowCutGap.AdaptivePackingUpdateHandover
import DirectedFlowCutGap.AdaptivePackingWeightInput
import DirectedFlowCutGap.AdaptivePackingWeightedData
import DirectedFlowCutGap.PackingAmountExecution
import DirectedFlowCutGap.PackingAmountProgram
import DirectedFlowCutGap.PackingLoadEntryExecution
import DirectedFlowCutGap.PackingLoadEntryProgram
import DirectedFlowCutGap.PackingLoadRowBounds
import DirectedFlowCutGap.PackingLoadRowHead
import DirectedFlowCutGap.PackingLoadRowProgram
import DirectedFlowCutGap.PackingLoadRowRefinement
import DirectedFlowCutGap.PackingLoadRowTail
import DirectedFlowCutGap.PackingLoadRowTrace
import DirectedFlowCutGap.ActualPackingEntry
import DirectedFlowCutGap.ActualPackingGuard
import DirectedFlowCutGap.ActualPackingUpdateRow
import DirectedFlowCutGap.PackingEntryBounds
import DirectedFlowCutGap.PackingEntryCalls
import DirectedFlowCutGap.PackingEntryConstants
import DirectedFlowCutGap.PackingEntryExecution
import DirectedFlowCutGap.PackingEntryProgram
import DirectedFlowCutGap.PackingGuardBounds
import DirectedFlowCutGap.PackingGuardComparison
import DirectedFlowCutGap.PackingGuardExecution
import DirectedFlowCutGap.PackingGuardProgram
import DirectedFlowCutGap.PackingGuardState
import DirectedFlowCutGap.PackingUpdateEntryCall
import DirectedFlowCutGap.PackingUpdateRowBounds
import DirectedFlowCutGap.PackingUpdateRowHead
import DirectedFlowCutGap.PackingUpdateRowProgram
import DirectedFlowCutGap.PackingUpdateRowRefinement
import DirectedFlowCutGap.PackingUpdateRowTail
import DirectedFlowCutGap.PackingUpdateRowTrace
import DirectedFlowCutGap.ActualPackingStart
import DirectedFlowCutGap.PackingGraphContext
import DirectedFlowCutGap.PackingStartBounds
import DirectedFlowCutGap.PackingStartCalls
import DirectedFlowCutGap.PackingStartExecution
import DirectedFlowCutGap.PackingStartFinalAllocation
import DirectedFlowCutGap.PackingStartGraphCalls
import DirectedFlowCutGap.PackingStartInitialOracle
import DirectedFlowCutGap.PackingStartInput
import DirectedFlowCutGap.PackingStartNormalizeState
import DirectedFlowCutGap.PackingStartProgram
import DirectedFlowCutGap.PackingStateRecord
import DirectedFlowCutGap.PackingZeroRowConstruction
import DirectedFlowCutGap.PackingZeroRowProgram
import DirectedFlowCutGap.ActualScalarQuotientRow
import DirectedFlowCutGap.ScalarQuotientRowBounds
import DirectedFlowCutGap.ScalarQuotientRowCall
import DirectedFlowCutGap.ScalarQuotientRowProgram
import DirectedFlowCutGap.ScalarQuotientRowRefinement
import DirectedFlowCutGap.ScalarQuotientRowTrace
import DirectedFlowCutGap.ActualNormalizedRow
import DirectedFlowCutGap.MaskedRationalRowBounds
import DirectedFlowCutGap.MaskedRationalRowHead
import DirectedFlowCutGap.MaskedRationalRowProgram
import DirectedFlowCutGap.MaskedRationalRowTrace
import DirectedFlowCutGap.NormalizedRowBounds
import DirectedFlowCutGap.NormalizedRowExecution
import DirectedFlowCutGap.NormalizedRowProgram
import DirectedFlowCutGap.ActualObjectiveRow
import DirectedFlowCutGap.ActualRationalProduct
import DirectedFlowCutGap.CanonicalRationalProductProgram
import DirectedFlowCutGap.CanonicalRationalProductReturn
import DirectedFlowCutGap.ObjectiveProductListBounds
import DirectedFlowCutGap.ObjectiveProductListProgram
import DirectedFlowCutGap.ObjectiveProductListTrace
import DirectedFlowCutGap.ObjectiveRowExecution
import DirectedFlowCutGap.ObjectiveRowProgram
import DirectedFlowCutGap.ActualRationalQuotient
import DirectedFlowCutGap.CanonicalRationalQuotientFinish
import DirectedFlowCutGap.CanonicalRationalQuotientPrefix
import DirectedFlowCutGap.CanonicalRationalQuotientProgram
import DirectedFlowCutGap.CanonicalRationalQuotientReturn
import DirectedFlowCutGap.OracleMaskProgram
import DirectedFlowCutGap.OracleMaskComparison
import DirectedFlowCutGap.OracleTailMembership
import DirectedFlowCutGap.OracleMaskTail
import DirectedFlowCutGap.OracleMaskVertex
import DirectedFlowCutGap.OracleMaskConstruction
import DirectedFlowCutGap.OracleMaskRefinement
import DirectedFlowCutGap.OracleMaskBounds
import DirectedFlowCutGap.ActualOracleMask
import DirectedFlowCutGap.CapacityBottleneckProgram
import DirectedFlowCutGap.CapacityCandidateStep
import DirectedFlowCutGap.CapacityCandidateConstruction
import DirectedFlowCutGap.CapacityBottleneckSelection
import DirectedFlowCutGap.CapacityBottleneckEncoding
import DirectedFlowCutGap.CapacityBottleneckRefinement
import DirectedFlowCutGap.CapacityBottleneckBounds
import DirectedFlowCutGap.ActualCapacityBottleneck
import DirectedFlowCutGap.DemandSelectionOrigin
import DirectedFlowCutGap.ActualDemandOrigin
import DirectedFlowCutGap.OracleChoiceProgram
import DirectedFlowCutGap.OracleChoiceCalls
import DirectedFlowCutGap.OracleDefaultMask
import DirectedFlowCutGap.OracleEmptyChoice
import DirectedFlowCutGap.OracleSelectedMask
import DirectedFlowCutGap.OracleChoiceData
import DirectedFlowCutGap.OracleCapacityCall
import DirectedFlowCutGap.OracleCapacityFinish
import DirectedFlowCutGap.OracleChoiceCapacity
import DirectedFlowCutGap.OracleChoiceExecution
import DirectedFlowCutGap.ActualOracleChoice
import DirectedFlowCutGap.GraphOracleProgram
import DirectedFlowCutGap.GraphOracleDemandCall
import DirectedFlowCutGap.GraphOracleChoiceCall
import DirectedFlowCutGap.GraphOracleExecution
import DirectedFlowCutGap.GraphOracleBounds
import DirectedFlowCutGap.ActualGraphOracle
import DirectedFlowCutGap.FractionalCoverRawOracleEncoding
import DirectedFlowCutGap.BinaryFractionalWalkBounds
import DirectedFlowCutGap.BinaryFractionalGraphBounds
import DirectedFlowCutGap.ActualDemandSelection
import DirectedFlowCutGap.ActualDemandSelectionBounded
import DirectedFlowCutGap.DemandCollectionBounds
import DirectedFlowCutGap.DemandCollectionData
import DirectedFlowCutGap.DemandCollectionExecution
import DirectedFlowCutGap.DemandCollectionProgram
import DirectedFlowCutGap.DemandCollectionRefinement
import DirectedFlowCutGap.DemandCollectionSelection
import DirectedFlowCutGap.DemandCollectionStep
import DirectedFlowCutGap.DemandQueryCall
import DirectedFlowCutGap.DemandQueryContext
import DirectedFlowCutGap.DemandRecordConstruction
import DirectedFlowCutGap.DemandSelectedPayload
import DirectedFlowCutGap.DemandSelectionRefinement
import DirectedFlowCutGap.SupportRecoveryProgram
import DirectedFlowCutGap.SupportSearchData
import DirectedFlowCutGap.SupportSearchAccounts
import DirectedFlowCutGap.SupportRecoveryCalls
import DirectedFlowCutGap.SupportSearchInvariants
import DirectedFlowCutGap.SupportEdgeComparison
import DirectedFlowCutGap.SupportEdgeMembership
import DirectedFlowCutGap.SupportAdjacencyTest
import DirectedFlowCutGap.SupportCodeLookup
import DirectedFlowCutGap.SupportPredecessorPrefix
import DirectedFlowCutGap.SupportPredecessorScan
import DirectedFlowCutGap.SupportVisitAllocation
import DirectedFlowCutGap.SupportVisitDecision
import DirectedFlowCutGap.SupportVertexVisit
import DirectedFlowCutGap.SupportForwardTransitions
import DirectedFlowCutGap.SupportForwardPass
import DirectedFlowCutGap.SupportRoundInitial
import DirectedFlowCutGap.SupportRounds
import DirectedFlowCutGap.SupportSearchExecution
import DirectedFlowCutGap.SupportSearchLowerMachine
import DirectedFlowCutGap.SupportRetainedData
import DirectedFlowCutGap.SupportSearchEncoding
import DirectedFlowCutGap.SupportRetainedScans
import DirectedFlowCutGap.SupportRetainedVisit
import DirectedFlowCutGap.SupportRetainedSearch
import DirectedFlowCutGap.SupportPrimitiveBounds
import DirectedFlowCutGap.SupportIterationBounds
import DirectedFlowCutGap.ActualSupportSearch
import DirectedFlowCutGap.RecoveredEdgeProjection
import DirectedFlowCutGap.CostedSupportProgram
import DirectedFlowCutGap.CostedSupportCalls
import DirectedFlowCutGap.CostedSupportContinuation
import DirectedFlowCutGap.CostedSupportExecution
import DirectedFlowCutGap.CostedSupportRefinement
import DirectedFlowCutGap.ActualCostedRecovery
import DirectedFlowCutGap.GraphRecoveryController
import DirectedFlowCutGap.GraphRecoveryContext
import DirectedFlowCutGap.GraphRecoveryCalls
import DirectedFlowCutGap.GraphRecoveryFinish
import DirectedFlowCutGap.GraphRecoveryRefinement
import DirectedFlowCutGap.GraphRecoveryExecution
import DirectedFlowCutGap.GraphRecoverySize
import DirectedFlowCutGap.GraphRecoveryBounds
import DirectedFlowCutGap.ActualGraphShortest
import DirectedFlowCutGap.GraphDiscoveryProgram
import DirectedFlowCutGap.GraphDiscoveryCalls
import DirectedFlowCutGap.GraphVertexDecision
import DirectedFlowCutGap.GraphPassConstruction
import DirectedFlowCutGap.GraphRoundData
import DirectedFlowCutGap.GraphRoundCalls
import DirectedFlowCutGap.GraphBoundedRounds
import DirectedFlowCutGap.GraphLookupCalls
import DirectedFlowCutGap.GraphLookupDecision
import DirectedFlowCutGap.GraphLookupScan
import DirectedFlowCutGap.GraphMinimizeConstruction
import DirectedFlowCutGap.GraphDiscoveryRefinement
import DirectedFlowCutGap.GraphDiscoveryWidths
import DirectedFlowCutGap.GraphDiscoveryBounds
import DirectedFlowCutGap.GraphRoundBounds
import DirectedFlowCutGap.GraphDiscoveryExecution
import DirectedFlowCutGap.ActualGraphDiscovery
import DirectedFlowCutGap.BinaryPointerListRead
import DirectedFlowCutGap.GraphAdjacencyProgram
import DirectedFlowCutGap.GraphWalkExtension
import DirectedFlowCutGap.GraphRelaxationProgram
import DirectedFlowCutGap.GraphRelaxationCalls
import DirectedFlowCutGap.GraphRelaxationAdapters
import DirectedFlowCutGap.GraphRelaxationFinish
import DirectedFlowCutGap.GraphRelaxationScan
import DirectedFlowCutGap.GraphRelaxationBounds
import DirectedFlowCutGap.GraphRelaxationExecution
import DirectedFlowCutGap.GraphRelaxationRefinement
import DirectedFlowCutGap.CostedCandidateMaterialization
import DirectedFlowCutGap.CostedCandidateSelection
import DirectedFlowCutGap.CostedCandidateBounds
import DirectedFlowCutGap.MaterializedGraphSelection
import DirectedFlowCutGap.IndexedRationalRead
import DirectedFlowCutGap.OutgoingCostProgram
import DirectedFlowCutGap.PathCostMaterialization
import DirectedFlowCutGap.MaterializedPathSum
import DirectedFlowCutGap.MaterializedGraphPath
import DirectedFlowCutGap.BinaryTrimProgram
import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.CanonicalRationalAddition
import DirectedFlowCutGap.CanonicalRationalSum
import DirectedFlowCutGap.CanonicalPathCost
import DirectedFlowCutGap.RetainedArgminProgram
import DirectedFlowCutGap.RetainedGraphArgmin
import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.RationalComparisonProgram
import DirectedFlowCutGap.InputRationalComparisonProgram
import DirectedFlowCutGap.RowTableValidationProgram
import DirectedFlowCutGap.SourceRowAcceptanceProgram
import DirectedFlowCutGap.ValidatedFractionalRows
import DirectedFlowCutGap.BinaryZeroProgram
import DirectedFlowCutGap.SourceRowValidationProgram
import DirectedFlowCutGap.BudgetOrderedPrefixProgram
import DirectedFlowCutGap.PackingBudgetProgram
import DirectedFlowCutGap.SourceRowReadProgram
import DirectedFlowCutGap.InputMultiplicationProgram
import DirectedFlowCutGap.InputAdditionProgram
import DirectedFlowCutGap.BinaryAdditionProgram
import DirectedFlowCutGap.SelfDelimitedWordProgram
import DirectedFlowCutGap.PreparedBinaryLength
import DirectedFlowCutGap.PreparedBinaryIncrement
import DirectedFlowCutGap.PreparedOrderedCounterPrefix
import DirectedFlowCutGap.PreparedRowEmit
import DirectedFlowCutGap.PreparedIndexedPairRead
import DirectedFlowCutGap.BinaryIndexedPairRead
import DirectedFlowCutGap.PreparedCounterPrefix
import DirectedFlowCutGap.FractionalHeapRead
import DirectedFlowCutGap.CounterPrefixProgram
import DirectedFlowCutGap.BinaryCounterProgram
import DirectedFlowCutGap.ConstructedPrefixMaterialization
import DirectedFlowCutGap.ReferencePrefixMaterialization
import DirectedFlowCutGap.PackedBooleanRead
import DirectedFlowCutGap.EncodedPackingBitBudget
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! The original inherited gates remain unchanged. This additional validator
combines their identical module-selection/axiom predicates and the new module's
unsafe predicate in one indexed module pass. ModuleData.constNames is the exact
source of imported ConstantInfo entries; final ownership and ConstantInfo are
resolved from the current environment, and duplicate names are excluded.
Full type/body closure edges are
memoized across roots; every root still visits its complete transitive closure. -/
set_option stderrAsMessages false
#eval IO.eprintln "GRID_ENVELOPE_FULL_IMPORT_READY"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted := `DirectedFlowCutGap.GridFamilyEnvelope
  let mut fullCount := 0
  let mut newCount := 0
  let mut auditedNames : NameSet := {}
  for module in modules do
    if (`DirectedFlowCutGap).isPrefixOf module then
      let some idx := env.getModuleIdx? module | throwError "Missing module index: {module}"
      let some data := env.header.moduleData[idx.toNat]? | throwError "Missing module data: {module}"
      for name in data.constNames do
        if env.getModuleIdxFor? name == some idx && !auditedNames.contains name then
          let some ci := env.find? name | throwError "Missing imported constant: {name}"
          auditedNames := auditedNames.insert name
          fullCount := fullCount+1
          for ax in ← Lean.collectAxioms name do
            unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
          if module == wanted then
            newCount := newCount+1
            if ci.isUnsafe then throwError "Unsafe new-module declaration: {name}"
          IO.eprintln s!"ATTR {module}|{name}"
  if fullCount == 0 then throwError "Reference source audit selected no declarations"
  if newCount == 0 then throwError "No declarations audited for {wanted}"
  IO.eprintln s!"PASS exhaustive reference closure axiom audit: {fullCount} declarations"
  IO.eprintln s!"GRID_ENVELOPE_MODULE_AUDIT passed: {wanted}; {newCount} declarations"
  IO.eprintln s!"GRID_ENVELOPE_DECLARATION_AUDIT passed: {newCount} declarations"
  let mut dependencies : NameMap (List Name) := {}
  let mut axiomNames : NameSet := {}
  for root in #[`DirectedFlowCutGap.GridFamilyEnvelope.row_bits, `DirectedFlowCutGap.GridFamilyEnvelope.fuel_length, `DirectedFlowCutGap.GridFamilyEnvelope.initial_range, `DirectedFlowCutGap.GridFamilyEnvelope.advance_range, `DirectedFlowCutGap.GridFamilyEnvelope.guess_bound, `DirectedFlowCutGap.GridFamilyEnvelope.loop_bound, `DirectedFlowCutGap.GridFamilyEnvelope.original_input_bound, `DirectedFlowCutGap.GridFamilyEnvelope.family_polynomial_bit, `DirectedFlowCutGap.GridFamilyEnvelope.instruction_mono, `DirectedFlowCutGap.GridFamilyEnvelope.instruction_diagonal_le_eval, `DirectedFlowCutGap.GridFamilyEnvelope.physical_eval, `DirectedFlowCutGap.GridFamilyEnvelope.physical_le_eval, `DirectedFlowCutGap.GridFamilyEnvelope.fixed_polynomial_bound, `DirectedFlowCutGap.GridFamilyEnvelope.family_fixed_polynomial_bit] do
    IO.eprintln s!"GRID_ENVELOPE_CLOSURE_BEGIN {root}"
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless seen.contains name do
        seen := seen.insert name
        let deps ← match dependencies.find? name with
          | some deps => pure deps
          | none => do
            let some ci := env.find? name | throwError "Missing closure constant: {name}"
            if ci.isUnsafe then throwError "Unsafe closure constant: {root}: {name}"
            match ci with
            | .axiomInfo _ =>
              axiomNames := axiomNames.insert name
              unless allowed.contains name do throwError "Forbidden closure axiom: {root}: {name}"
            | _ => pure ()
            let deps := ci.getUsedConstantsAsSet.toList
            dependencies := dependencies.insert name deps
            pure deps
        if axiomNames.contains name then axioms := axioms.insert name
        for dep in deps do
          unless seen.contains dep do todo := todo.push dep
    IO.eprintln s!"GRID_ENVELOPE_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"

/-! Numerical-envelope checks only. These do not execute a physical machine. -/
namespace DirectedFlowCutGap.GridEnvelopeSmoke
open BinaryArithmetic BinaryRational GridFamilyEnvelope

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def paddedZero : Fraction := ⟨[false,false,false],[true,false,false],by decide⟩
def paddedHalf : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩

def checkInput (name : String) (d : ℕ) (rows : List Fraction) : IO Unit := do
  let S := LambdaRowProgram.rowBits rows
  let W := wordBound rows.length S
  let fuel := GridFamilyInput.fuel rows
  let old := GridFamilyInput.inputSteps d rows
  let bound := instructionBound d rows.length S
  unless fuel.length≤W && value fuel≤W && value fuel==LambdaGridProgram.gridLimit rows &&
      GridInputProgram.inputSteps rows==prefixBound rows.length S &&
      OriginalRowMinimum.inputSteps rows==minimumBound rows.length S && old≤bound do
    throw (IO.userError ("FAILED numerical original-input envelope "++name))
  IO.println ("PASS numerical original-input envelope "++name++" grid-length="++toString (value fuel))

def checkController (name : String) (d : ℕ) (rows : List Fraction) (exp fuel : Bits) (W : ℕ) : IO Unit := do
  let L := LambdaGridProgram.gridLimit rows
  unless value exp+value fuel≤L && exp.length+value fuel≤W && fuel.length≤W do
    throw (IO.userError ("BAD fixture controller preconditions "++name))
  unless GridFamily.instructionBound d rows exp fuel≤
      (value fuel+1)*bodyBound d rows.length (LambdaRowProgram.rowBits rows) W do
    throw (IO.userError ("FAILED numerical recursive envelope "++name))
  let mut e := exp
  let mut f := fuel
  for _ in List.range (value fuel+1) do
    unless value e+value f≤L && e.length+value f≤W && f.length≤W do
      throw (IO.userError ("FAILED conserved controller invariant "++name))
    unless (isZero f).1 do
      e := (increment true e).1
      f := (predecessor f).1
  unless value f==0 do throw (IO.userError ("FAILED controller termination "++name))
  IO.println ("PASS numerical controller envelope "++name)

def main : IO Unit := do
  checkInput "empty" 0 []
  checkInput "zero" 0 [zero]
  checkInput "padded-zero" 1 [paddedZero]
  checkInput "one" 0 [one]
  checkInput "one-demand" 1 [one]
  checkInput "half-padded" 1 [paddedHalf]
  checkInput "mixed" 3 [paddedZero,frac 5 2,one]
  checkInput "four-rationals" 7 [frac 31 7,frac 8 4,paddedHalf,frac 0 9]
  checkController "zero-fuel-padded" 1 [one] [] [false,false,false,false] 30
  checkController "padded-positive-fuel" 2 [paddedHalf] [] ((GridFamilyInput.fuel [paddedHalf])++[false,false,false]) 40
  checkController "nonzero-exponent-padded" 2 [paddedHalf] [true,false,false] [true,false,true,false] 40
  checkController "last-singleton" 2 [one] (LambdaGridProgram.gridLimit [one]-1).bits [true,false,false] 40
end DirectedFlowCutGap.GridEnvelopeSmoke

#eval DirectedFlowCutGap.GridEnvelopeSmoke.main
