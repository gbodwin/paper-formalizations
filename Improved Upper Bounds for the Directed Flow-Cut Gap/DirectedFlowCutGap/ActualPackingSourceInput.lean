import DirectedFlowCutGap.PackingSourceInputExecution

namespace DirectedFlowCutGap.PackingSourceInput
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal WordPairTableRead

def inputSize (capacity matrix demands : List (Bits × Bits)) : ℕ :=
  SourceRowTableProgram.bits capacity+SourceRowTableProgram.bits matrix+
    SourceRowTableProgram.bits demands+capacity.length+matrix.length+demands.length

theorem instructions_le (capacity matrix demands : List (Bits × Bits)) :
    instructions capacity matrix demands≤29*inputSize capacity matrix demands+31 := by
  simp only [instructions,inputSize,SourceRowTableProgram.steps]
  omega

def initial (source : Bits) : BitState 64 := ⟨[],[],⟨[],[],[],[]⟩,[],48,source⟩

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The same physical source-driven run allocates all three primitive lists;
all source requests and the final halt are included in its paid budget. -/
theorem prepare_bit (capacity matrix demands : List (Bits × Bits)) (suffix : Bits) :
    ∃ charge out, Run program (instructions capacity matrix demands) charge
      (initial (encode capacity matrix demands++suffix))
      ((encode capacity matrix demands).map Event.request) out ∧
      Table (eraseState out).heap (eraseState out).registers.a capacity ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState out).registers.c
        (matrix.map Prod.fst) ∧
      Table (eraseState out).heap (eraseState out).registers.d demands ∧
      out.source=suffix ∧ out.stack=[] ∧ out.pc=56 ∧
      value out.next=out.heap.length ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 64 1 0
        (29*inputSize capacity matrix demands+31) := by
  obtain ⟨ext,cap,mat,dem,high,hc,hm,hd⟩ := prepare capacity matrix demands suffix [] 0 0 0 0 0 rfl
  have start : state [] 0 0 0 0 0 [] (encode capacity matrix demands++suffix) 48=
      eraseState (initial (encode capacity matrix demands++suffix)) := by rfl
  rw [start] at high
  have halt : tickNatural program (state ([]++ext) (0+ext.length) cap mat mat dem [] suffix 56)=none := by
    simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,_⟩ := polynomial_simulation
    (initial_bounded (encode capacity matrix demands++suffix)) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2.trans
      (SupportSearchEncoding.complete_mono 64 1 0 _ _ (instructions_le capacity matrix demands))⟩
  · simpa only [erase,state] using hc
  · simpa only [erase,state] using hm
  · simpa only [erase,state] using hd
  · have h : (eraseState out).source=suffix := by rw [erase];rfl
    exact h
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=56 := by rw [erase];rfl
    exact h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];simp [state]
    simpa [eraseState,State.map] using h

end DirectedFlowCutGap.PackingSourceInput
