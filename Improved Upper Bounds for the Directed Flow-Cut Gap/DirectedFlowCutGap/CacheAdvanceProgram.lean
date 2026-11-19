import DirectedFlowCutGap.CacheInstallProgram
import DirectedFlowCutGap.EpochScanBounds

/-! The ready gate makes weight installation and a new solve conditional. -/

namespace DirectedFlowCutGap.CacheAdvanceProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (Parameters parameters_extend)
open EpochScanData (Graph Stored stored_extend cacheOf candidateWords optimizer)
open CandidateEnumeration (Node Network)

def gateLabel (pc : Fin 298) : Fin 7288 := ⟨64+pc.val,by omega⟩
def installLabel (pc : Fin 48) : Fin 7288 := ⟨362+pc.val,by omega⟩
def refreshLabel (pc : Fin 6878) : Fin 7288 := ⟨410+pc.val,by omega⟩

def program : Program 7288 := fun pc =>
  if pc.val < 64 then
    match pc.val with
    | 0 => .call (gateLabel 0) 1 .r0
    | 1 => .field .r0 .r0 false 2
    | 2 => .branch .r0 4 6 3 4
    | 6 => .call (installLabel 0) 7 .r1
    | 7 => .call (refreshLabel 2) 3 .r3
    | _ => .halt
  else if h : pc.val < 362 then
    if pc.val=68 then .ret .r3
    else ReferenceProgramLabels.instruction gateLabel (CacheGatesProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val < 410 then
    if pc.val=365 then .ret .r3
    else ReferenceProgramLabels.instruction installLabel (CacheInstallProgram.program ⟨pc.val-362,by omega⟩)
  else if pc.val=414 then .ret .r3
  else ReferenceProgramLabels.instruction refreshLabel (AdaptiveRoundRefreshProgram.program ⟨pc.val-410,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 7288

def freshBound (n L scale : ℕ) : ℕ :=
  CandidateRefreshProgram.instructionBound n L n.size L.size (scale+2)

def allocationBound (n L B scale ratio threshold : ℕ) : ℕ :=
  CacheGatesProgram.allocationBound (EpochScanBounds.currentWidth n B) (EpochScanBounds.optimumWidth n L) ratio threshold+
    freshBound n L scale+24

def instructionBound (n L H B scale ratio threshold : ℕ) : ℕ :=
  CacheGatesProgram.instructionBound H (EpochScanBounds.currentWidth n B) (EpochScanBounds.optimumWidth n L) ratio threshold+
    freshBound n L scale+55

private theorem gate_slots (pc : Fin 298) (h : CacheGatesProgram.program pc≠.halt) :
    program (gateLabel pc)=ReferenceProgramLabels.instruction gateLabel (CacheGatesProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,gateLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<362 by omega,show 64+pc.val≠68 by omega]

private theorem install_slots (pc : Fin 48) (h : CacheInstallProgram.program pc≠.halt) :
    program (installLabel pc)=ReferenceProgramLabels.instruction installLabel (CacheInstallProgram.program pc) := by
  by_cases stop : pc.val=3
  · have eq : pc=3 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,installLabel,show ¬362+pc.val<64 by omega,show ¬362+pc.val<362 by omega,
      show 362+pc.val<410 by omega,show 362+pc.val≠365 by omega]

private theorem refresh_slots (pc : Fin 6878) (h : AdaptiveRoundRefreshProgram.program pc≠.halt) :
    program (refreshLabel pc)=ReferenceProgramLabels.instruction refreshLabel (AdaptiveRoundRefreshProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,refreshLabel,show ¬410+pc.val<64 by omega,show ¬410+pc.val<362 by omega,
      show ¬410+pc.val<410 by omega,show 410+pc.val≠414 by omega]

noncomputable abbrev nextCode {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)} (positive : 0<L)
    (E : ResidualSearch.Enumeration (Network n L)) (R : Bits) (s : Code (Graph adj) demands L) :
    Code (Graph adj) demands L :=
  (IntegerAdaptiveExecution.advance (optimizer (adj:=adj) (demands:=demands) positive E) (value R) (cacheOf positive E s)).cache.state

theorem advance_exact {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}
    (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R : Bits) (s : Code (Graph adj) demands L) :
    (IntegerAdaptiveExecution.advance (optimizer (adj:=adj) (demands:=demands) positive E) (value R) (cacheOf positive E s)).cache =
      cacheOf positive E (nextCode positive E R s) := by
  unfold nextCode IntegerAdaptiveExecution.advance
  split
  · rfl
  · rfl

theorem fresh_mono (n L : ℕ) {s S : ℕ} (h : s≤S) : freshBound n L s ≤ freshBound n L S := by
  unfold freshBound CandidateRefreshProgram.instructionBound CandidateFamilyProgram.instructionBound
    CandidateFamilyScanProgram.instructionBound CandidateFamilyScanProgram.rowLimit CandidateDemandRowProgram.instructionBound
    CandidateRawSolverProgram.instructionBound CandidateCapacityMatrixProgram.instructionBound
    CandidateCapacitySetupProgram.instructionBound CandidateCapacityTableProgram.instructionBound
    CandidateCapacityTableProgram.tableBound CandidateCapacityTableProgram.rowBound CandidateCapacityCellProgram.instructionBound
    CandidateDescriptorCapacityProgram.instructionBound CandidateCoreCapacityProgram.instructionBound
  gcongr

private theorem gate_bounds (H R M : ℕ) {cur cur' opt opt' : ℕ} (hc : cur≤cur') (ho : opt≤opt') :
    CacheGatesProgram.allocationBound cur opt R M ≤ CacheGatesProgram.allocationBound cur' opt' R M ∧
    CacheGatesProgram.instructionBound H cur opt R M ≤ CacheGatesProgram.instructionBound H cur' opt' R M := by
  unfold CacheGatesProgram.allocationBound CacheGatesProgram.instructionBound AdaptiveGatesProgram.instructionBound
    BinaryProductOrderProgram.instructionBound
  constructor <;> gcongr

set_option maxHeartbeats 2500000 in
theorem natural_advance {n L B : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}
    (s : Code (Graph adj) demands L) (positive : 0<L) (EN : ResidualSearch.Enumeration (Node n L))
    (E : ResidualSearch.Enumeration (Network n L)) {R M scale : Bits} {words : List (List Bits)}
    (params : Parameters (L:=L) heap r.c adj R M) (cache : Stored heap r.d s positive EN E words scale)
    (grid : max L.size (L+1).size≤B) (widths : ∀ ws ∈ words,∀ w ∈ ws,w.length≤B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root scratch live k : ℕ) (nextWords : List (List Bits)) (nextScale : Bits),
      Stored (heap++ext) root (nextCode positive E R s) positive EN E nextWords nextScale ∧
      (∀ ws ∈ nextWords,∀ w ∈ ws,w.length≤B) ∧ nextScale.length≤ scale.length+2 ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) ⟨scratch,live,r.c,root⟩ [] tape 3) ∧
      k ≤ instructionBound n L heap.length B scale.length R.length M.length ∧
      ext.length ≤ allocationBound n L B scale.length R.length M.length := by
  let c := cacheOf positive E s
  obtain ⟨cm,om⟩ := EpochScanBounds.mass_widths cache widths
  obtain ⟨eg,regs,result,g,rep,gateRun,gateTime,gateAlloc⟩ := CacheGatesProgram.natural_cache_gates params cache tape
  obtain ⟨allocation,time⟩ := gate_bounds heap.length R.length M.length cm om
  have gt := gateTime.trans time
  have ga := gateAlloc.trans allocation
  let mid := heap++eg
  let withGate := r.set .r0 result
  have invoke := ReferenceProgramInvocation.call gateLabel gate_slots (caller:=0) (continuation:=1)
    (result:=.r3) (dst:=.r0) (by rfl) (by rfl) [] gateRun
  have gated : NaturalRun program (g+2) (state heap r [] tape 0) [] (state mid withGate [] tape 1) := by
    simpa only [mid,withGate,Registers.get,Registers.set] using invoke
  obtain ⟨ready,active,atResult,readyAt,activeAt⟩ := rep
  let args := r.set .r0 ready
  have atGate : mid[result]?=some (.pair ready active) := atResult
  have getReady : tickNatural program (state mid withGate [] tape 1)=some ⟨state mid args [] tape 2,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,withGate,args,atGate]
  have test : mid[ready]?=some (.flag (c.ready (value R))) := readyAt
  by_cases h : c.ready (value R)=true
  · have nextEq : nextCode positive E R s=s := by
      change (IntegerAdaptiveExecution.advance _ (value R) c).cache.state=s
      simp only [IntegerAdaptiveExecution.advance,ite_eq_left h]
      rfl
    have branch : tickNatural program (state mid args [] tape 2)=some ⟨state mid args [] tape 3,[],0⟩ := by
      simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,test,h,tagBranch]
    refine ⟨eg,r.d,ready,r.b,g+2+2,words,scale,nextEq.symm ▸ stored_extend cache eg,widths,by omega,?_,?_,?_⟩
    · simpa only [args,Registers.set,List.nil_append] using append_run gated (.step getReady (.step branch (.done _)))
    · unfold instructionBound
      omega
    · unfold allocationBound
      omega
  · have no : c.ready (value R)=false := Bool.eq_false_iff.mpr h
    have nextEq : nextCode positive E R s=c.install := by
      change (IntegerAdaptiveExecution.advance _ (value R) c).cache.state=c.install
      simp only [IntegerAdaptiveExecution.advance,ite_eq_right h]
      rfl
    have branch : tickNatural program (state mid args [] tape 2)=some ⟨state mid args [] tape 6,[],0⟩ := by
      simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,test,no,tagBranch]
    obtain ⟨ei,live,packed,runtime,six,_,installed,installRun⟩ := CacheInstallProgram.natural_install (r:=args)
      (stored_extend cache eg) tape
    let grown := mid++ei
    let reload := args.set .r1 live
    have callInstall := ReferenceProgramInvocation.call installLabel install_slots (caller:=6) (continuation:=7)
      (result:=.r3) (dst:=.r1) (by rfl) (by rfl) [] installRun
    have install : NaturalRun program 30 (state mid args [] tape 6) []
        (state grown reload [] tape 7) := by
      simpa only [grown,reload,Registers.get] using callInstall
    have newParams : Parameters (L:=L) grown reload.c adj R M := parameters_extend (parameters_extend params eg) ei
    let nextScale := false::false::scale
    let nextWords := candidateWords EN E s
    have represented : AdaptiveControllerStorage.StateAt grown reload.b c.install.data nextWords nextScale := installed
    obtain ⟨er,root,k,output,refreshRun,refreshTime⟩ := AdaptiveRoundRefreshProgram.natural_cache_from_state
      (r:=reload) c.install positive EN E represented newParams tape
    have callRefresh := ReferenceProgramInvocation.call refreshLabel refresh_slots (caller:=7) (continuation:=3)
      (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] refreshRun
    have concrete : NaturalRun program (k+2) (state grown reload [] tape 7) []
        (state (grown++er) ⟨ready,live,r.c,root⟩ [] tape 3) := by
      simpa only [reload,args,Registers.get,Registers.set] using callRefresh
    have growth := ControllerWordWidth.extension_bound refreshRun rfl
    have candidateWidth := CandidateFamilyData.family_width (L:=L) ⟨adj,s.data.cut⟩ s.data.remaining (4*s.data.scale) L.bits EN E
    rw [Nat.size_eq_bits_len] at candidateWidth
    have kt : k≤ freshBound n L scale.length+18 := by
      simpa only [freshBound,nextScale,List.length_cons] using refreshTime
    refine ⟨eg++ei++er,root,ready,live,g+2+(30+(k+2)+1+1),nextWords,nextScale,?_,?_,by simp [nextScale],?_,?_,?_⟩
    · rw [nextEq]
      have representedCache : Stored (grown++er) root c.install positive EN E nextWords nextScale := output
      simpa only [mid,grown,List.append_assoc] using representedCache
    · exact fun ws hws w hw => (candidateWidth ws hws w hw).trans grid
    · simpa only [mid,grown,List.append_assoc,List.nil_append] using
        append_run gated (.step getReady (.step branch (append_run install concrete)))
    · unfold instructionBound
      omega
    · simp only [List.length_append,allocationBound]
      omega

end DirectedFlowCutGap.CacheAdvanceProgram
