import DirectedFlowCutGap.PackingRunStartWidth

namespace DirectedFlowCutGap.PackingRun
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)
open RationalComparisonProgram

theorem start_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap scalar input d : ℕ}
    (capRep : StoredList heap cap capacity.toList) (deltaRep : Stored heap scalar delta)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (next : ℕ) (dense : next=heap.length) (source : Bits)
    (saved : Registers ℕ) (pc : Fin 7960) (stack : List (Frame ℕ 7960)) :
    ∃ k ext root,
      NaturalRun program (k+1)
        (state heap next cap scalar input d (⟨pc,.r1,saved⟩::stack) source 3020) []
        (state (heap++ext) (next+ext.length) saved.a root saved.c saved.d stack source pc) ∧
      PackingStart.StateRecord (heap++ext) root label
        (BinaryFractionalCore.start capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).1 ∧
      (∀ B,1≤B → (∀ i,(label i).length≤B) → StoredBounded delta B →
        (∀ x∈capacity.toList,StoredBounded x B) → k≤PackingStart.instructionBound ds.length n B) := by
  obtain ⟨ot,out,run,src,st,outpc,nd,⟨ext,he⟩,rep,ob⟩ := PackingStart.start_high adjacency capacity delta label numeric hn encoded
    (PackingStart.state heap next cap scalar input d [] source 3020) rfl dense rfl capRep deltaRep inputRep
  have terminal : PackingStart.program out.pc=.halt := by
    rw [outpc]
    rfl
  have lifted := child_return startLabel PackingStart.program start_slots run rfl st
    .r3 .r1 saved pc stack (start_halt out.pc terminal)
  simp only [PackingStart.state] at he src
  have nn : out.next=next+ext.length := by rw [nd,he,List.length_append,←dense]
  have entry : startLabel 3020=(3020 : Fin 7960) := by decide
  refine ⟨ScalarQuotientRow.steps true delta capacity.toList+ot+25+
    PackingStart.finishSteps capacity (initial capacity delta).1
      (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn (initial capacity delta).1).1,ext,out.registers.d,?_,?_,?_⟩
  · simpa only [PackingStart.state,entry,state,he,nn,src,Registers.set,Registers.get] using lifted
  · simpa only [he] using rep
  · intro B hB labels deltaWidth caps
    exact PackingStart.start_steps_bound adjacency capacity delta label hn ds ot B hB labels deltaWidth caps ob
end DirectedFlowCutGap.PackingRun
