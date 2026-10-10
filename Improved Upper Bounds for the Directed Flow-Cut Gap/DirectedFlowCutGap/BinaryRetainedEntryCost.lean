import DirectedFlowCutGap.BinaryRetainedRoundingCost
import DirectedFlowCutGap.EncodedRoundingRepetition

/-!
# Shared-ledger entry and repetition bounds

The existing generic-monad entry and repetition are instantiated directly with
the actual StateT Ledger PMF callback. One ledger survives every repeated draw.
The proof counts every returned entry and the total Result.sampling field;
selected.sampling is not substituted for the complete repeated charge.

The uniform charge is derived from a finite reached-width reserve. No fresh
physical ledger or stateless sampler law is assumed between entries. These
remain declared component charges until the documented representation and
same-stream realization obligations are connected.
-/
namespace DirectedFlowCutGap.BinaryRetainedEntryCost
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape BinaryRetainedTapeCost
open BinaryRetainedRoundingCost RetainedGridState IntegerAdaptiveExecution
open EncodedRoundingEntry EncodedRoundingBounds EncodedRoundingInput

set_option backward.isDefEq.respectTransparency false

def epochBudget (n : ℕ) : ℕ := IntegerEpochParameters.fuel n+1

def totalCallbacks (n extra : ℕ) : ℕ := (extra+1)*epochBudget n

def coreBound (n L : ℕ) (fuel cutoff : Bits) (S C : ℕ) : ℕ :=
  deterministicBound n L (epochBudget n) (epochBudget n) (IntegerEpochParameters.fuel n)+
    commonCharge n fuel cutoff S C*epochBudget n

/-- The callback count is a proof witness from the actual input log. It does
not add an executed counter to the entry's output. -/
def EntryCertificate {n : ℕ} (fuel cutoff : Bits) (S C j B : ℕ)
    (s : Ledger) (out : Output n × Ledger) : Prop :=
  ∃ k ≤ epochBudget n,
    ledgerWidth out.2 ≤ reachedWidth n fuel cutoff S (j+k) ∧
    value out.2.draws ≤ value s.draws+drawBudget n*k ∧
    out.2.operations=s.operations+out.1.sampling ∧
    out.1.sampling ≤ k*commonCharge n fuel cutoff S C ∧
    out.1.operations ≤ B ∧ out.1.vertices.length ≤ n

noncomputable section
variable {n L : ℕ}

/-- Actual core entry, with the same constructed factory and prepared mask.
The stateful support theorem supplies its deterministic work envelope. -/
theorem entry_bounds [NeZero L] (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (adjacency : PairFlags n) (hL : 0<L)
    (S C j : ℕ) (s : Ledger) (hslots : j+epochBudget n ≤ C)
    (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : Output n × Ledger}
    (hout : out ∈ ((EncodedRoundingEntry.run (callback bit fuel cutoff hcut hL)
      adjacency hL).run s).support) :
    EntryCertificate fuel cutoff S C j (coreBound n L fuel cutoff S C) s out := by
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨d,hd,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  let F := CandidateEnumeration.make n L
  let initial := prepare F.base.enumeration adjacency hL
  have hd' : d ∈ ((EncodedSampledRounding.runSampled adjacency F
      (CandidateEnumeration.fin_vertices n) hL (callback bit fuel cutoff hcut hL)
      (IntegerEpochParameters.restart n) (epochBudget n) (epochBudget n) initial.state).run s).support := by
    simpa only [EncodedEpochParameters.compute_restart,EncodedEpochParameters.compute_fuel] using hd
  have hc := BinaryRetainedRoundingCost.run_bounds adjacency F
    (CandidateEnumeration.fin_vertices n) hL bit fuel cutoff hcut
    (IntegerEpochParameters.restart n) (epochBudget n) (epochBudget n) initial.state
    S C j s hslots hs hd'
  have hlog := BinaryRetainedRoundingCost.run_support adjacency F
    (CandidateEnumeration.fin_vertices n) hL (callback bit fuel cutoff hcut hL)
    (IntegerEpochParameters.restart n) (epochBudget n) (epochBudget n) initial.state s hd'
  have hp := sampled_price_bound adjacency F (CandidateEnumeration.fin_vertices n) hL
    (IntegerEpochParameters.restart n) (epochBudget n) (epochBudget n)
    (IntegerEpochParameters.fuel n) (IntegerClosureAsymptotic.restart_nnreal_one_lt n)
    initial.state (EncodedRoundingEntry.prepared_mass F.base.enumeration adjacency hL) hlog
  have hparams := EncodedEpochParameters.compute_bound n
  have hfactory := CandidateEnumeration.make_work n L
  have hprep := prepare_bound F.base.enumeration adjacency hL
  have hdraws := hc.draws_eq
  have hdrawBound := hc.draws_le
  have hsampling := hc.sampling
  have htotalSampling : d.1.sampling ≤ commonCharge n fuel cutoff S C*epochBudget n := by
    have h := Nat.mul_le_mul_right (commonCharge n fuel cutoff S C) hc.calls
    nlinarith
  refine ⟨d.1.logged.inputs.length,hc.calls,hc.width,?_,hc.ledger_charge,hc.sampling,?_,?_⟩
  · omega
  · -- The price envelope already reserves 10*epochs+1. Combine that
    -- reserve with the sampled interpreter's +16, leaving exactly +6 here.
    have hcontroller : d.1.operations ≤
        controllerBound n L (epochBudget n) (epochBudget n) (IntegerEpochParameters.fuel n)+
          epochBudget n*(EncodedTapeMaterialization.materializationBound n+6)+d.1.sampling := by
      have hwork := hc.work
      nlinarith only [hwork,hp]
    change (EncodedEpochParameters.compute n).work+F.work+initial.work+
      d.1.operations+(12*n+4)+8 ≤ coreBound n L fuel cutoff S C
    change F.work = 120*n*(L+1)+155*n+6*L+127 at hfactory
    change initial.work ≤ preparationBound n at hprep
    unfold coreBound deterministicBound
    nlinarith only [hparams,hfactory,hprep,hcontroller,htotalSampling]
  · have hn := output_nodup d.1.logged.result.cache.state.data.cut
    simpa only [List.toFinset_card_of_nodup hn,Fintype.card_fin] using
      (output d.1.logged.result.cache.state.data.cut).1.toFinset.card_le_univ

/-- Easy branches use no callback and leave the ledger exactly unchanged.
The hard branch reuses the stateful core certificate. -/
theorem allRegime_bounds [NeZero L] (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (adjacency : PairFlags n) (hL : 0<L)
    (S C j : ℕ) (s : Ledger) (hslots : j+epochBudget n ≤ C)
    (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : Output n × Ledger}
    (hout : out ∈ ((EncodedAllRegimeRounding.run (callback bit fuel cutoff hcut hL)
      adjacency hL).run s).support) :
    EntryCertificate fuel cutoff S C j
      (EncodedAllRegimeRounding.operationBound n (commonCharge n fuel cutoff S C)) s out := by
  simp only [EncodedAllRegimeRounding.run] at hout
  split_ifs at hout with hn hLn hHard
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    refine ⟨0,Nat.zero_le _,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.add_zero] using hs
    · simp only [Nat.mul_zero,Nat.add_zero,le_refl]
    · rfl
    · exact Nat.zero_le _
    · unfold EncodedAllRegimeRounding.operationBound EncodedAllRegimeRounding.emptyOutput
      dsimp only
      omega
    · exact Nat.zero_le _
  · change out ∈ (PMF.bind _ _).support at hout
    obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    obtain ⟨k,hk,hw,hd,hl,hsamp,hop,hlen⟩ :=
      entry_bounds bit fuel cutoff hcut adjacency hL S C j s hslots hs hr
    refine ⟨k,hk,hw,hd,hl,hsamp,?_,hlen⟩
    have hp := EncodedEpochParameters.compute_bound n
    have hpoly := deterministic_polynomial n L hLn
    have hf := fuel_le_cubic n
    have hmul := Nat.mul_le_mul_left (commonCharge n fuel cutoff S C)
      (show epochBudget n ≤ n^3+2 by unfold epochBudget; omega)
    change deterministicBound n L (epochBudget n) (epochBudget n)
      (IntegerEpochParameters.fuel n) ≤ naturalPolynomial n at hpoly
    unfold coreBound at hop
    unfold EncodedAllRegimeRounding.operationBound
    dsimp only
    nlinarith only [hop,hp,hpoly,hmul]
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    refine ⟨0,Nat.zero_le _,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.add_zero] using hs
    · simp only [Nat.mul_zero,Nat.add_zero,le_refl]
    · rfl
    · exact Nat.zero_le _
    · have hp := EncodedEpochParameters.compute_bound n
      unfold EncodedAllRegimeRounding.operationBound EncodedAllRegimeRounding.universalOutput
      dsimp only
      omega
    · simp only [EncodedAllRegimeRounding.universalOutput,List.length_finRange,le_refl]
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    refine ⟨0,Nat.zero_le _,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.add_zero] using hs
    · simp only [Nat.mul_zero,Nat.add_zero,le_refl]
    · rfl
    · exact Nat.zero_le _
    · unfold EncodedAllRegimeRounding.operationBound EncodedAllRegimeRounding.emptyOutput
      dsimp only
      omega
    · exact Nat.zero_le _

/-- State-sensitive counterpart of drawMany_facts for this exact entry.
Every recursive entry receives the ledger produced by its predecessor. -/
theorem drawMany_bounds [NeZero L] (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (adjacency : PairFlags n) (hL : 0<L)
    (S C j entries : ℕ) (s : Ledger) (hslots : j+entries*epochBudget n ≤ C)
    (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : EncodedRoundingRepetition.Batch n × Ledger}
    (hout : out ∈ ((EncodedRoundingRepetition.drawMany
      (EncodedAllRegimeRounding.run (callback bit fuel cutoff hcut hL) adjacency hL)
      entries).run s).support) :
    ∃ k ≤ entries*epochBudget n,
      out.1.outputs.length=entries ∧
      ledgerWidth out.2 ≤ reachedWidth n fuel cutoff S (j+k) ∧
      value out.2.draws ≤ value s.draws+drawBudget n*k ∧
      out.2.operations=s.operations+out.1.sampling ∧
      out.1.sampling ≤ k*commonCharge n fuel cutoff S C ∧
      out.1.operations ≤ entries*(EncodedAllRegimeRounding.operationBound n
        (commonCharge n fuel cutoff S C)+12)+1 ∧
      ∀ o ∈ out.1.outputs, o.vertices.length ≤ n := by
  induction entries generalizing j s out with
  | zero =>
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      refine ⟨0,by simp,by simp,?_,?_,?_,?_,?_,?_⟩
      · simpa only [Nat.add_zero] using hs
      · simp only [Nat.mul_zero,Nat.add_zero,le_refl]
      · rfl
      · exact Nat.zero_le _
      · simp only [zero_mul,Nat.zero_add,le_refl]
      · simp only [List.not_mem_nil,false_implies,implies_true]
  | succ entries ih =>
      change out ∈ (PMF.bind _ _).support at hout
      obtain ⟨first,hfirst,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨tail,htail,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      have hfirstSlots : j+epochBudget n ≤ C := by
        rw [Nat.add_mul,one_mul] at hslots
        omega
      obtain ⟨k,hk,hw,hd,hl,hsamp,hop,hlen⟩ :=
        allRegime_bounds bit fuel cutoff hcut adjacency hL S C j s hfirstSlots hs hfirst
      have htailSlots : j+k+entries*epochBudget n ≤ C := by
        rw [Nat.add_mul,one_mul] at hslots
        omega
      obtain ⟨q,hq,hcount,hwidth,hdraw,hledger,hsampling,hwork,hshape⟩ :=
        ih (j := j+k) (s := first.2) htailSlots hw htail
      refine ⟨k+q,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [Nat.add_mul,one_mul]
        omega
      · simpa only [List.length_cons] using congrArg (fun v => v+1) hcount
      · simpa only [Nat.add_assoc] using hwidth
      · change value tail.2.draws ≤ value s.draws+drawBudget n*(k+q)
        rw [Nat.mul_add]
        omega
      · change tail.2.operations=s.operations+(first.1.sampling+tail.1.sampling)
        omega
      · change first.1.sampling+tail.1.sampling ≤ (k+q)*commonCharge n fuel cutoff S C
        rw [Nat.add_mul]
        omega
      · change first.1.operations+tail.1.operations+12 ≤ _
        rw [Nat.add_mul,one_mul]
        omega
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hlen
        · exact hshape o ho

/-- Exactly extra+1 entries share the ledger, then the existing counted
first-tie selector runs once. All repeated charges remain in Result.sampling. -/
theorem repeat_bounds [NeZero L] (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (adjacency : PairFlags n) (hL : 0<L)
    (S C j extra : ℕ) (s : Ledger) (hslots : j+(extra+1)*epochBudget n ≤ C)
    (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : EncodedRoundingRepetition.Result n × Ledger}
    (hout : out ∈ ((EncodedRoundingRepetition.run (callback bit fuel cutoff hcut hL)
      adjacency hL extra).run s).support) :
    ∃ k ≤ (extra+1)*epochBudget n,
      out.1.samples.length=extra+1 ∧ out.1.selected∈out.1.samples ∧
      (∀ o ∈ out.1.samples, out.1.selected.vertices.length ≤ o.vertices.length) ∧
      ledgerWidth out.2 ≤ reachedWidth n fuel cutoff S (j+k) ∧
      value out.2.draws ≤ value s.draws+drawBudget n*k ∧
      out.2.operations=s.operations+out.1.sampling ∧
      out.1.sampling ≤ k*commonCharge n fuel cutoff S C ∧
      out.1.operations ≤ (extra+1)*(EncodedAllRegimeRounding.operationBound n
        (commonCharge n fuel cutoff S C)+4*n+28)+10 := by
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨first,hfirst,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨rest,hrest,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have hfirstSlots : j+epochBudget n ≤ C := by
    rw [Nat.add_mul,one_mul] at hslots
    omega
  obtain ⟨k,hk,hw,hd,hl,hsamp,hop,hlen⟩ :=
    allRegime_bounds bit fuel cutoff hcut adjacency hL S C j s hfirstSlots hs hfirst
  have htailSlots : j+k+extra*epochBudget n ≤ C := by
    rw [Nat.add_mul,one_mul] at hslots
    omega
  obtain ⟨q,hq,hcount,hwidth,hdraw,hledger,hsampling,hwork,hshape⟩ :=
    drawMany_bounds bit fuel cutoff hcut adjacency hL S C (j+k) extra first.2
      htailSlots hw hrest
  have hall : ∀ o ∈ first.1::rest.1.outputs, o.vertices.length ≤ n := by
    intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hlen
    · exact hshape o ho
  have hselect := EncodedRoundingRepetition.select_bound first.1 rest.1.outputs n hall
  refine ⟨k+q,?_,?_,EncodedRoundingRepetition.select_member _ _,
    EncodedRoundingRepetition.select_minimum _ _,?_,?_,?_,?_,?_⟩
  · rw [Nat.add_mul,one_mul]
    omega
  · simpa only [List.length_cons] using congrArg (fun v => v+1) hcount
  · simpa only [Nat.add_assoc] using hwidth
  · change value rest.2.draws ≤ value s.draws+drawBudget n*(k+q)
    rw [Nat.mul_add]
    omega
  · change rest.2.operations=s.operations+(first.1.sampling+rest.1.sampling)
    omega
  · change first.1.sampling+rest.1.sampling ≤ (k+q)*commonCharge n fuel cutoff S C
    rw [Nat.add_mul]
    omega
  · change first.1.operations+rest.1.operations+
      (EncodedRoundingRepetition.select first.1 rest.1.outputs).2+8 ≤ _
    rw [hcount] at hselect
    nlinarith

/-- Closed budget for the actual repeated StateT entry, from an arbitrary
initial ledger. Its physical padding is paid through the initial width. -/
theorem run_bound [NeZero L] (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (adjacency : PairFlags n) (hL : 0<L)
    (extra : ℕ) (s : Ledger) {out : EncodedRoundingRepetition.Result n × Ledger}
    (hout : out ∈ ((EncodedRoundingRepetition.run (callback bit fuel cutoff hcut hL)
      adjacency hL extra).run s).support) :
    let C := totalCallbacks n extra
    let K := commonCharge n fuel cutoff (ledgerWidth s) C
    ledgerWidth out.2 ≤ reachedWidth n fuel cutoff (ledgerWidth s) C ∧
      value out.2.draws ≤ value s.draws+drawBudget n*C ∧
      out.2.operations=s.operations+out.1.sampling ∧
      out.1.sampling ≤ C*K ∧
      out.1.operations ≤ (extra+1)*(EncodedAllRegimeRounding.operationBound n K+4*n+28)+10 := by
  obtain ⟨k,hk,_,_,_,hw,hd,hl,hsamp,hop⟩ :=
    repeat_bounds bit fuel cutoff hcut adjacency hL (ledgerWidth s)
      (totalCallbacks n extra) 0 extra s (by simp only [Nat.zero_add,totalCallbacks,le_refl])
      (by simp only [reachedWidth,zero_mul,Nat.add_zero,le_refl]) hout
  have hm := reachedWidth_mono n fuel cutoff (ledgerWidth s) hk
  have hdraw := Nat.mul_le_mul_left (drawBudget n) hk
  have hcharge := Nat.mul_le_mul_right
    (commonCharge n fuel cutoff (ledgerWidth s) (totalCallbacks n extra)) hk
  refine ⟨?_,?_,hl,?_,hop⟩
  · have hw' : ledgerWidth out.2 ≤ reachedWidth n fuel cutoff (ledgerWidth s) k := by
      simpa only [Nat.zero_add] using hw
    exact hw'.trans hm
  · exact hd.trans (Nat.add_le_add_left hdraw (value s.draws))
  · exact hsamp.trans hcharge

end
end DirectedFlowCutGap.BinaryRetainedEntryCost
