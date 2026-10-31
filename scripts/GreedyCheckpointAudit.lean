import GreedyShortcuts.ChainStrictJoinGuardV2
import GreedyShortcuts.ChainSharedPivotGuardV2
import GreedyShortcuts.ChainCertifiedRootProjection
import GreedyShortcuts.ChainSharedPivotRootProjectionV2
import GreedyShortcuts.ChainGuardCone
import GreedyShortcuts.ChainProjectedConeOwners
import GreedyShortcuts.ChainPrefixSavings
import GreedyShortcuts.ChainMaximumChildSelector
import GreedyShortcuts.ChainOwnerLastRootTail
import GreedyShortcuts.ChainFixedRootSuffix
import GreedyShortcuts.ChainCoalescingRootSuffix
import GreedyShortcuts.ChainRootTailHeadOrder
import GreedyShortcuts.ChainSuffixCharging
import GreedyShortcuts.ChainLevels
import GreedyShortcuts.ChainEntryLevels
import GreedyShortcuts.ChainRootMinimumCorridor
import GreedyShortcuts.ChainOriginalMinimumTailStep
import GreedyShortcuts.ChainFiniteOriginalSelectorHistory
import GreedyShortcuts.ChainOriginalRankBand
import GreedyShortcuts.ChainOriginalRetiredBands
import GreedyShortcuts.ChainOriginalTraceRemoval
import GreedyShortcuts.ChainOriginalOwnerTailExterior
import GreedyShortcuts.ChainTailInteriorSavings
import GreedyShortcuts.ChainInteriorSavings
import GreedyShortcuts.ChainOriginalCutCandidate
import GreedyShortcuts.ChainCanonicalOwnerGroup
import GreedyShortcuts.ChainRectangleCharging
import GreedyShortcuts.ChainCanonicalOwnerCut
import GreedyShortcuts.ChainCanonicalExteriorIncidence
import GreedyShortcuts.ChainCanonicalCohortCoverage
import GreedyShortcuts.ChainCanonicalProfitableEndpoints
import GreedyShortcuts.ChainCanonicalEndpointPressure
import GreedyShortcuts.ChainCanonicalTracePressure
import GreedyShortcuts.ChainCanonicalSuffixCounts
import GreedyShortcuts.ChainCanonicalMidpointPressure
import Lean.Util.CollectAxioms

open Lean Elab Command

/-
Logical/static checkpoint only: fixed-H/original-ROOT trace bookkeeping and
one legal original-source insertion offer.
The 20-theorem stored dependency finding concerns pinned preintegration artifacts
identified by independent metadata receipt SHA256
2ca6f629746470c5976322dcf46b3d841e36bc9df22379a3e7a39f8a08c566be;
it is not a metadata rerun on future CI oleans. Standard pinned replay excludes
two generated partial helpers and provides no per-declaration skip counts.
This checkpoint makes no compiled execution-equivalence or termination claim
for originalTraceStepAt, its _sunfold, or either partial implementation.
The owner-tail/interior extension proves local actual-row head/count and
one-edge saving claims. Its 33 safe/nonpartial, initially absent declarations
were observed only in pinned local outputs, not future CI or exact skip telemetry.
The accepted sibling is imported and audited too: its scalar API and client
coexist with the separately named conjunction API; no old declaration is replaced.
The owner-cut extension adds17 source-level declarations constructing ONE actual
fixed-H/one-owner legal candidate offer. It supplies no cumulative payment,
useful-population, weighted/time or phase conclusion, nor any runtime refinement.
The canonical-cohort extension proves an actual same-edge physical rectangle
with each original source OLD minimum and FIRST admission derived. Its selected
cut supplies the literal cohort factor; only cohort.card>=1 is guaranteed.
Useful cohort coverage, weighted/copy/time payment and runtime refinement remain
open. Eight original Group theorem statements are unchanged (seven by-proof
headers plus the unchanged term-bodied witness). No phase bound is asserted.
The physical nonterminal incidence extension reindexes actual (owner,head)
pairs after deleting W and proves total cohort incidence >=OwnerCount*(Delta-2).
Its maximum-cardinality witness is not assumed long or profitable. No payment
or runtime refinement follows; all previous holds remain.
The profitable-endpoint extension discards at most one additional short
center per row. It derives active incidence >=OwnerCount*(Delta-3), and every
active center supplies a legal fresh endpoint edge paying its cohort. Finite
averaging selects ONE actual candidate with the active-center-card denominator;
alternative scores are never spent as summed progress. Cohort size>=1, useful
scale, cumulative payment, runtime refinement and phase holds remain unchanged.
The endpoint-pressure extension adds17 safe/nonpartial declarations deriving
a triangular actual-row saving inventory, not new coverage. Under SAME actual
step/owner hypotheses with Delta>=4, ONE actual maximum endpoint gain satisfies
OwnerCount*(Delta-2)*(Delta-3)<=2*LongCenters.card*actual_gain. LongCenters.card
is retained; only original target W is counted. Useful-scale amplification,
cumulative weighted/copy/time payment and runtime/phase holds remain open.
The trace-pressure extension adds50 safe/nonpartial declarations for ONE
fixed H/ROOT trace. Actual Delta>=4 centers retain their pooled cardinality:
Mass<=2*Family.card*ONE actual maximum gain, with the zero-mass alternative
Drop<=3*traceLength. Family.card equals the sum of qualifying LongCenters.card
and Family.card+traceLength+terminalCone.card<=initialCone.card. This is
candidate pressure, not cumulative selected payment or extra cone stock.
Any separate HAND sharpness example is an UNVERIFIED ILLUSTRATION, outside
kernel-checked claims; it is not acceptance evidence for an unproved claim.
Target amplification, weighted/time payment, runtime and phase remain open.
All 18 existing executable modules, three fixtures and standard CI controls
remain mandatory and unchanged. No original-paper operational contract is waived.
Original-scale, weighted owner/copy/time payment and whole-phase/paper obligations
remain open. The unfiltered axiom audit below still covers both partial helpers.
-/

run_cmd do
  let env ← getEnv
  -- Lazy equation theorems can be exported by multiple modules. Import order
  -- chooses their defining-module attribution, not their type/proof/axioms.
  -- Counts below describe the stable declarations; this required theorem is
  -- still included in the unfiltered, complete axiom-audit loop below.
  let shared := `GreedyShortcuts.ChainDistance.Context.count.eq_1
  let some sharedInfo := env.find? shared
    | throwError "Missing required shared generated declaration {shared}"
  match sharedInfo with
  | .thmInfo _ => pure ()
  | _ => throwError "Required shared generated declaration is not a theorem: {shared}"
  let some sharedIdx := env.getModuleIdxFor? shared
    | throwError "Missing defining module for {shared}"
  let sharedOwner := env.allImportedModuleNames[sharedIdx.toNat]!
  unless sharedOwner == `GreedyShortcuts.ChainStrictJoinGuardV2 ||
      sharedOwner == `GreedyShortcuts.ChainEntryLevels do
    throwError "Unexpected defining module {sharedOwner} for {shared}"
  logInfo m!"CHECKPOINT_SHARED_GENERATED {shared} OWNER {sharedOwner}"
  for (moduleName, expected) in #[(`GreedyShortcuts.ChainStrictJoinGuardV2, 9),
                                  (`GreedyShortcuts.ChainSharedPivotGuardV2, 3),
                                  (`GreedyShortcuts.ChainCertifiedRootProjection, 5),
                                  (`GreedyShortcuts.ChainSharedPivotRootProjectionV2, 1),
                                  (`GreedyShortcuts.ChainGuardCone, 9),
                                  (`GreedyShortcuts.ChainProjectedConeOwners, 7),
                                  (`GreedyShortcuts.ChainPrefixSavings, 9),
                                  (`GreedyShortcuts.ChainMaximumChildSelector, 9),
                                  (`GreedyShortcuts.ChainOwnerLastRootTail, 44),
                                  (`GreedyShortcuts.ChainFixedRootSuffix, 15),
                                  (`GreedyShortcuts.ChainCoalescingRootSuffix, 25),
                                  (`GreedyShortcuts.ChainRootTailHeadOrder, 24),
                                  (`GreedyShortcuts.ChainSuffixCharging, 5),
                                  (`GreedyShortcuts.ChainLevels, 18),
                                  (`GreedyShortcuts.ChainEntryLevels, 12),
                                  (`GreedyShortcuts.ChainRootMinimumCorridor, 27),
                                  (`GreedyShortcuts.ChainOriginalMinimumTailStep, 21),
                                  (`GreedyShortcuts.ChainFiniteOriginalSelectorHistory, 114),
                                  (`GreedyShortcuts.ChainOriginalRankBand, 38),
                                  (`GreedyShortcuts.ChainOriginalRetiredBands, 33),
                                  (`GreedyShortcuts.ChainOriginalTraceRemoval, 61),
                                  (`GreedyShortcuts.ChainOriginalOwnerTailExterior, 20),
                                  (`GreedyShortcuts.ChainTailInteriorSavings, 13),
                                  (`GreedyShortcuts.ChainInteriorSavings, 5),
                                  (`GreedyShortcuts.ChainOriginalCutCandidate, 17),
                                  (`GreedyShortcuts.ChainCanonicalOwnerGroup, 16),
                                  (`GreedyShortcuts.ChainRectangleCharging, 2),
                                  (`GreedyShortcuts.ChainCanonicalOwnerCut, 17),
                                  (`GreedyShortcuts.ChainCanonicalExteriorIncidence, 19),
                                  (`GreedyShortcuts.ChainCanonicalCohortCoverage, 5),
                                  (`GreedyShortcuts.ChainCanonicalProfitableEndpoints, 18),
                                  (`GreedyShortcuts.ChainCanonicalEndpointPressure, 17),
                                  (`GreedyShortcuts.ChainCanonicalTracePressure, 50)] do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing checkpoint module {moduleName}"
    let decls := env.constants.toList.filter (fun x => env.getModuleIdxFor? x.1 == some idx)
    let stableDecls := decls.filter (fun x => x.1 != shared)
    let requiredNames : Array String :=
      if moduleName == `GreedyShortcuts.ChainStrictJoinGuardV2 then
        #["GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_7",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_8",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._simp_1_2",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._simp_1_4",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._simp_1_5",
          "_private.GreedyShortcuts.ChainStrictJoinGuardV2.0.GreedyShortcuts.ChainDistance.Context.strictJoinV2_last_rejected_split"]
      else if moduleName == `GreedyShortcuts.ChainEntryLevels then
        #["GreedyShortcuts.ChainDistance.Context.count_take_mono",
          "GreedyShortcuts.ChainDistance.Context.count_take_zero_le",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_7",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_8",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_9",
          "GreedyShortcuts.ChainDistance.Context.minimum_take"]
      else if moduleName == `GreedyShortcuts.ChainOriginalCutCandidate then
        #["GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.exists_originalOwnerCut_bank._proof_1_7",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCutCandidateHeads",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCutCandidateHeads_card",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCutCandidateHeads_card._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCut_short_or_positive_bank",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCut_short_or_positive_bank._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCut_short_or_positive_bank._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCut_short_or_positive_bank._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCut_short_or_positive_bank._proof_1_4",
          "_private.GreedyShortcuts.ChainOriginalCutCandidate.0.GreedyShortcuts.ChainDistance.Context.rootImportant_mem_tailHeads"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalOwnerGroup then
        #["GreedyShortcuts.ChainDistance.Context.mem_originalOwnerCanonicalGroup",
          "GreedyShortcuts.ChainDistance.Context.mem_originalOwnerCanonicalGroup._simp_1_2",
          "GreedyShortcuts.ChainDistance.Context.mem_originalOwnerCanonicalGroup._simp_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalGroup",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalGroup.eq_1",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalGroup_coalesces",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalGroup_row",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalGroup_terminal",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalGroup_witness",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalPrefix",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalTail",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalTail._proof_1",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalTail_display",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerSharedSuffix",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerSharedSuffix_root",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerSharedSuffix_terminal"]
      else if moduleName == `GreedyShortcuts.ChainRectangleCharging then
        #["GreedyShortcuts.ChainDistance.Context.rectangle_drop_lower_bound",
          "GreedyShortcuts.ChainDistance.Context.rectangle_insertion_drop"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalOwnerCut then
        #["GreedyShortcuts.ChainDistance.Context.originalCanonicalCutHeads",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCutHeads_bound",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCutHeads_bound._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCutSources",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCutSources_card",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_7",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalCut_short_or_cohort_offer._proof_1_8",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_cut_bank",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_cut_bank._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_cut_bank._proof_1_2"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalExteriorIncidence then
        #["GreedyShortcuts.ChainDistance.Context.mem_originalCanonicalPhysicalExterior",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalExterior_subset_cut",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalPhysicalExterior",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalPhysicalExterior_W_debit",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalPhysicalExterior_W_debit._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalPhysicalExterior_drop",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalPhysicalExterior_order",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalPhysicalExterior_order_injective",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalTail_root",
          "GreedyShortcuts.ChainDistance.Context.rootTailExterior_physical_marker",
          "GreedyShortcuts.ChainDistance.Context.rootTailExterior_physical_marker._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.rootTailExterior_physical_marker._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.rootTailExterior_physical_marker._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.rootTailExterior_physical_marker._simp_1_1",
          "GreedyShortcuts.ChainDistance.Context.rootTailExterior_physical_marker._simp_1_2",
          "GreedyShortcuts.ChainDistance.Context.rootTailPhysicalExterior",
          "GreedyShortcuts.ChainDistance.Context.rootTailPhysicalExterior_of_important_start",
          "_private.GreedyShortcuts.ChainCanonicalExteriorIncidence.0.GreedyShortcuts.ChainDistance.Context.coverage_heads_physical",
          "_private.GreedyShortcuts.ChainCanonicalExteriorIncidence.0.GreedyShortcuts.ChainDistance.Context.coverage_important_mem_heads"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalCohortCoverage then
        #["GreedyShortcuts.ChainDistance.Context.exists_originalCanonical_nonterminal_average",
          "GreedyShortcuts.ChainDistance.Context.exists_originalCanonical_nonterminal_average._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_nonterminal_coverage",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_nonterminal_coverage._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_nonterminal_incidence"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalProfitableEndpoints then
        #["GreedyShortcuts.ChainDistance.Context.exists_originalCanonical_profitable_endpoint_pressure",
          "GreedyShortcuts.ChainDistance.Context.exists_originalCanonical_profitable_endpoint_pressure._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalLongCenters",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_earlier_is_long",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_earlier_is_long._simp_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_earlier_is_long._simp_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_endpoint_bank",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_endpoint_bank._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_endpoint_bank._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_endpoint_bank._simp_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_endpoint_card",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_incidence_coverage",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_row_coverage",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_long_row_coverage._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_short_centers_card",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerCanonicalPrefix.congr_simp",
          "GreedyShortcuts.ChainDistance.Context.originalOwnerSharedSuffix.congr_simp",
          "_private.GreedyShortcuts.ChainCanonicalProfitableEndpoints.0.GreedyShortcuts.ChainDistance.Context.endpoint_important_head"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalEndpointPressure then
        #["GreedyShortcuts.ChainDistance.Context.exists_originalCanonical_triangular_endpoint_pressure",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_endpoint_owner_sum",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_later_heads_saving",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_later_heads_saving._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_later_heads_saving._simp_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_owner_target_important",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_row_triangular_pressure",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_row_triangular_pressure._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_row_triangular_pressure._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_row_triangular_pressure._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalCanonical_triangular_endpoint_inventory",
          "_private.GreedyShortcuts.ChainCanonicalEndpointPressure.0.GreedyShortcuts.ChainDistance.Context.twice_sum_later",
          "_private.GreedyShortcuts.ChainCanonicalEndpointPressure.0.GreedyShortcuts.ChainDistance.Context.twice_sum_later._proof_1_4",
          "_private.GreedyShortcuts.ChainCanonicalEndpointPressure.0.GreedyShortcuts.ChainDistance.Context.twice_sum_later._proof_1_5",
          "_private.GreedyShortcuts.ChainCanonicalEndpointPressure.0.GreedyShortcuts.ChainDistance.Context.twice_sum_later._simp_1_1",
          "_private.GreedyShortcuts.ChainCanonicalEndpointPressure.0.GreedyShortcuts.ChainDistance.Context.twice_sum_later._simp_1_2",
          "_private.GreedyShortcuts.ChainCanonicalEndpointPressure.0.GreedyShortcuts.ChainDistance.Context.twice_sum_later._simp_1_3"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalTracePressure then
        #["GreedyShortcuts.ChainDistance.Context.originalQualifiedStepCenters",
          "GreedyShortcuts.ChainDistance.Context.originalQualifiedStepCenters.eq_1",
          "GreedyShortcuts.ChainDistance.Context.originalQualifiedStepCenters_subset",
          "GreedyShortcuts.ChainDistance.Context.originalQualifiedStepCenters_target_debit",
          "GreedyShortcuts.ChainDistance.Context.originalQualifiedStepCenters_target_debit._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalStepEndpointMass",
          "GreedyShortcuts.ChainDistance.Context.originalStepEndpointMass.eq_1",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointCenterCount",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointCenterCount._f",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointCenterCount._sunfold",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointCenterCount.eq_1",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointCenterCount.eq_2",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointCenterCount.eq_def",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily._f",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily._sunfold",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.eq_1",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.eq_2",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.eq_def",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.match_1",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily_bank",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily_injective_card",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily_removed",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointMass",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointMass._f",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointMass._sunfold",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointMass.eq_1",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointMass.eq_2",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpointMass.eq_def",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_mass_inventory",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pool_capacity",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pool_capacity._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pool_capacity._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pressure_alternative",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pressure_alternative._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pressure_alternative._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_pressure_alternative._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_rank_debit",
          "GreedyShortcuts.ChainDistance.Context.originalTraceEndpoint_rank_debit._proof_1_4",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.match_1.eq_1",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.match_1.eq_2",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.originalTraceEndpointFamily.match_1.splitter",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_inventory",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_inventory._proof_1_2",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_rank_debit",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_rank_debit._proof_1_1",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_rank_debit._proof_1_3",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_rank_debit._proof_1_4",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.step_endpoint_rank_debit._simp_1_2",
          "_private.GreedyShortcuts.ChainCanonicalTracePressure.0.GreedyShortcuts.ChainDistance.Context.trace_endpoint_separated"]
      else #[]
    for required in requiredNames do
      unless stableDecls.any (fun x => x.1.toString == required) do
        throwError "Missing required checkpoint declaration {required} from {moduleName}"
    unless stableDecls.length == expected do
      throwError "Unexpected stable declaration coverage for {moduleName}: {stableDecls.length}"
    for (name, info) in decls do
      if info.isAxiom then throwError "Declared axiom {name}"
      if (moduleName == `GreedyShortcuts.ChainCanonicalEndpointPressure ||
          moduleName == `GreedyShortcuts.ChainCanonicalTracePressure) &&
          (info.isUnsafe || info.isPartial) then
        throwError "Unsafe or partial endpoint-pressure declaration {name}"
      let axioms ← collectAxioms name
      logInfo m!"CHECKPOINT_DECL {name} AXIOMS {axioms}"
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"CHECKPOINT_MODULE {moduleName} DECLARATIONS {decls.length} STABLE_DECLARATIONS {stableDecls.length}"

#print axioms GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2
#print axioms GreedyShortcuts.ChainDistance.Context.selected_pivot_suffix_prices_v2
#print axioms GreedyShortcuts.ChainDistance.Context.selected_shared_pivot_last_guard_offpath_v2

/-
For ONE actual canonical cohort and its shared fixed-ROOT suffix q with N>=3,
choose a real attained middle chain level. Remaining distinct physical target
heads are derived, not assumed. The same fresh legal edge satisfies
4*gain >= cohort.card*(N-2)^2 while retaining each original-source OLD minimum,
FIRST filter and both joins. Only cohort.card>=1 is inherited: useful cohort
coverage, original-scale/source amplification, cumulative weighted/time payment,
lookup implementation refinement and whole-phase/paper conclusions stay open.
The standalone objects have15+12 declarations. The one shared generated
originalOwnerSharedSuffix.congr_simp theorem is already audited and required
by the unchanged earlier ProfitableEndpoints block. Its complete stored type,
proof and axioms matched in pinned standalone/combined local observations.
This added block requires all26 genuinely new Names; future import attribution
changes must be diagnosed from actual names/types/axioms, never waived by a
blind count adjustment. Standard replay shortcut qualifications remain unchanged.
-/
run_cmd do
  let env ← getEnv
  for (moduleName, expected) in #[(`GreedyShortcuts.ChainCanonicalSuffixCounts,15),
      (`GreedyShortcuts.ChainCanonicalMidpointPressure,11)] do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing midpoint checkpoint module {moduleName}"
    let decls := env.constants.toList.filter fun x => env.getModuleIdxFor? x.1 == some idx
    let requiredNames : Array String :=
      if moduleName == `GreedyShortcuts.ChainCanonicalSuffixCounts then
        #["GreedyShortcuts.ChainDistance.Context.fixedRootSuffixMinimum_prefix",
          "GreedyShortcuts.ChainDistance.Context.fixedRootSuffixMinimum_prefix._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.fixedRootSuffix_level_split",
          "GreedyShortcuts.ChainDistance.Context.fixedRootSuffix_level_split._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.fixedRootSuffix_level_split._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.fixedRootSuffix_level_split._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.rootSuffix_exists_important_prefix_count",
          "GreedyShortcuts.ChainDistance.Context.rootSuffix_exists_important_prefix_count._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.rootSuffix_exists_important_prefix_count._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.rootSuffix_exists_important_prefix_count._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.rootSuffix_prefix_level_important",
          "GreedyShortcuts.ChainDistance.Context.rootSuffix_prefix_level_important._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.rootTailHeads_of_important_mem",
          "GreedyShortcuts.ChainDistance.Context.rootTailHeads_physical",
          "GreedyShortcuts.ChainDistance.Context.rootTailHeads_suffix_targets"]
      else if moduleName == `GreedyShortcuts.ChainCanonicalMidpointPressure then
        #["GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_exact_level_pressure",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_exact_level_pressure._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_exact_level_pressure._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_exact_level_pressure._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure._proof_1_2",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.originalCanonicalGroup_midpoint_pressure._proof_1_7"]
      else #[]
    unless decls.length == expected do
      throwError "Unexpected midpoint declaration coverage for {moduleName}: {decls.length}"
    for required in requiredNames do
      unless decls.any (fun x => x.1.toString == required) do
        throwError "Missing required midpoint declaration {required} from {moduleName}"
    for (name, info) in decls do
      if info.isAxiom || info.isUnsafe || info.isPartial then
        throwError "Rejected midpoint checkpoint declaration {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Unexpected midpoint axiom {ax} in {name}"
      logInfo m!"CHECKPOINT_DECL {name} AXIOMS {axioms}"
    logInfo m!"CHECKPOINT_MODULE {moduleName} DECLARATIONS {decls.length} STABLE_DECLARATIONS {decls.length}"
