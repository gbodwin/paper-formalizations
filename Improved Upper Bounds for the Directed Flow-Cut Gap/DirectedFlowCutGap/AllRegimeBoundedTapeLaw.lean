import DirectedFlowCutGap.EncodedBoundedTapeLaw
import DirectedFlowCutGap.EncodedAllRegimeRounding

/-!
# Guarded rounding under the actual bounded fair-bit callback

The exact entry guards select a finite tree before any sampling. All easy
branches are deterministic; the hard branch is the actual prepared core.
Only the returned finite cut is observed, keeping physical ledgers and cost
records unrestricted. These statements do not substitute a physical storage
runtime model or supply the remaining weighted-provider construction.
-/
namespace DirectedFlowCutGap.AllRegimeBoundedTapeLaw
noncomputable section
open RetainedGridState EncodedIntegerShortestPaths EncodedRoundingInput EncodedRoundingBounds
open BinaryArithmetic BinarySamplerMetadata BinaryWeightedSamplingLaw
open StatefulSamplerProjection EncodedBoundedTapeLaw

set_option backward.isDefEq.respectTransparency false
variable {n L : ℕ}

def drawBudget (n : ℕ) : ℕ := (IntegerEpochParameters.fuel n+1)*(2*n*n)

def tree (adjacency : PairFlags n) (hL : 0<L) : FiniteDrawTrees.Tree (Finset (Fin n)) :=
  if n=0 then .pure ∅ else
    if L ≤ n then
      if 64*IntegerEpochParameters.cap n ≤ L ∧ n ≤ L^3 then coreTree adjacency hL
      else .pure Finset.univ
    else .pure ∅

theorem cut_law (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger) :
    (observe (EncodedAllRegimeRounding.run
      (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL) state).map
      (fun out => out.vertices.toFinset) =
      FiniteDrawTrees.actual (value fuel) (tree adjacency hL) := by
  simp only [EncodedAllRegimeRounding.run,tree,EncodedEpochParameters.compute_cap]
  split_ifs with hn hLn hHard
  · simp only [observe_pure,PMF.pure_map,EncodedAllRegimeRounding.emptyOutput,
      List.toFinset_nil,FiniteDrawTrees.actual,FiniteDrawTrees.law]
  · simpa only [observe_map,PMF.map_comp,Function.comp_def] using
      entry_cut_law fuel cutoff hcut adjacency hL state
  · simp only [observe_pure,PMF.pure_map,EncodedAllRegimeRounding.universalOutput_set,FiniteDrawTrees.actual,FiniteDrawTrees.law]
  · simp only [observe_pure,PMF.pure_map,EncodedAllRegimeRounding.emptyOutput,
      List.toFinset_nil,FiniteDrawTrees.actual,FiniteDrawTrees.law]

theorem tree_ideal [NeZero L] (adjacency : PairFlags n) (hL : 0<L) :
    FiniteDrawTrees.ideal (tree adjacency hL) =
      IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration := by
  by_cases hn : n=0
  · subst n
    have hLn : ¬ L ≤ 0 := by omega
    simp only [tree,ite_true,IntegerClosureAsymptotic.allRegimeLaw,Fintype.card_fin,
      ite_eq_right hLn,FiniteDrawTrees.ideal,FiniteDrawTrees.law]
  · simp only [tree,hn,ite_false,IntegerClosureAsymptotic.allRegimeLaw,Fintype.card_fin]
    split_ifs with hLn hHard
    · exact coreTree_ideal adjacency hL
    · rfl
    · rfl

theorem core_within (adjacency : PairFlags n) (hL : 0<L) :
    FiniteDrawTrees.Within (drawBudget n) (coreTree adjacency hL) := by
  exact FiniteDrawTrees.within_map
    (RetainedDrawTrees.runTree_within
      (RetainedCandidateSolver.optimizer adjacency (CandidateEnumeration.make n L)
        (CandidateEnumeration.fin_vertices n) hL) hL
      (cutOracle (CandidateEnumeration.make n L).base.enumeration adjacency hL)
      (IntegerEpochParameters.restart n) (IntegerEpochParameters.fuel n+1)
      (IntegerEpochParameters.fuel n+1)
      (prepare (CandidateEnumeration.make n L).base.enumeration adjacency hL).state) _

theorem tree_within (adjacency : PairFlags n) (hL : 0<L) :
    FiniteDrawTrees.Within (drawBudget n) (tree adjacency hL) := by
  unfold tree
  split_ifs
  · exact .pure _ _
  · exact core_within adjacency hL
  · exact .pure _ _
  · exact .pure _ _

theorem event_le [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger)
    (P : Finset (Fin n) → Prop) :
    FiniteAmplification.probability
      ((observe (EncodedAllRegimeRounding.run
        (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL) state).map
        (fun out => out.vertices.toFinset)) P ≤
      FiniteAmplification.probability
        (IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
          (CandidateEnumeration.make n L).network.enumeration) P +
        (drawBudget n : ℝ)*((1 : ℝ)/2)^(value fuel) := by
  rw [cut_law]
  have h := FiniteDrawTrees.event_le (tree_within adjacency hL) (value fuel) P
  rw [tree_ideal] at h
  exact h

/-- Every real entry output is duplicate-free, independently of its sampler's bias. -/
theorem entry_nodup (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger)
    {out : EncodedRoundingEntry.Output n × Ledger}
    (hout : out ∈ ((EncodedRoundingEntry.run
      (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL).run state).support) :
    out.1.vertices.Nodup := by
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨d,hd,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  exact output_nodup _

theorem output_nodup (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger)
    {out : EncodedRoundingEntry.Output n × Ledger}
    (hout : out ∈ ((EncodedAllRegimeRounding.run
      (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL).run state).support) :
    out.1.vertices.Nodup := by
  simp only [EncodedAllRegimeRounding.run] at hout
  split_ifs at hout with hn hLn hHard
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    exact List.nodup_nil
  · change out ∈ (PMF.bind _ _).support at hout
    obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    exact entry_nodup fuel cutoff hcut adjacency hL state hr
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    exact List.nodup_finRange n
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    exact List.nodup_nil

private theorem map_eq_on_support {A B : Type} (p : PMF A) (f g : A → B)
    (h : ∀ a ∈ p.support, f a=g a) : p.map f=p.map g := by
  classical
  ext b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz := (PMF.apply_eq_zero_iff p a).mpr ha
    simp only [hz,ite_self]

/-- The observable length law is independent of the entering ledger, although
complete output records and their charges need not have that property. -/
theorem length_law (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger) :
    (observe (EncodedAllRegimeRounding.run
      (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL) state).map
      (fun out => out.vertices.length) =
      (FiniteDrawTrees.actual (value fuel) (tree adjacency hL)).map Finset.card := by
  let p := observe (EncodedAllRegimeRounding.run
    (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL) state
  have hshape (o) (ho : o ∈ p.support) : o.vertices.Nodup := by
    obtain ⟨out,hout,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    exact output_nodup fuel cutoff hcut adjacency hL state hout
  have h := map_eq_on_support p (fun o => o.vertices.length)
    (fun o => o.vertices.toFinset.card)
    (fun o ho => (List.toFinset_card_of_nodup (hshape o ho)).symm)
  rw [h]
  change p.map (Finset.card ∘ (fun o => o.vertices.toFinset)) = _
  rw [← PMF.map_comp,cut_law]

end
end DirectedFlowCutGap.AllRegimeBoundedTapeLaw
