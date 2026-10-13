import DirectedFlowCutGap.AdaptivePackingUpdateHandover

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem actual_load_output {n : ℕ} (label : Fin n → Bits) (q : BinaryFractionalCore.Choice n)
    (weights best loads : Row n) (cost total amount : Fraction) (events : List (BinaryFractionalCore.Event n))
    {heap : NaturalHeap} {frame qr ar er wr br cr tr lr mask ctx d : ℕ}
    (qp : HeapPath heap frame [true,true,true,true,true,true,false] qr)
    (ap : HeapPath heap frame [true,true,true,true,true,false] ar)
    (ep : HeapPath heap frame [true,true,true,true,true,true,true,true,false,true,true,true,true,true] er)
    (tp : HeapPath heap frame [false] tr)
    (cp : HeapPath heap frame [true,true,false,true] cr)
    (bp : HeapPath heap frame [true,true,false,false] br)
    (wp : HeapPath heap frame [true,false] wr)
    (qrRep : OracleChoice.StoredChoice heap qr label q) (arRep : Stored heap ar amount)
    (erRep : PackingStart.EventList heap label er events)
    (wrRep : StoredList heap wr weights.toList) (brRep : StoredList heap br best.toList)
    (crRep : Stored heap cr cost) (trRep : Stored heap tr total) (lrRep : StoredList heap lr loads.toList)
    (maskRep : BoolList heap mask q.mask.toList) (context : heap[ctx]?=some (.pair mask ar))
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext out,ext.length=PackingLoadRow.cells amount loads.toList q.mask.toList+8 ∧
      NaturalRun program (PackingLoadRow.steps amount loads.toList q.mask.toList+57)
        (state heap next lr ctx frame d stack source 4550) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.source=source ∧ out.stack=stack ∧ out.pc=4605 ∧
      PackingStart.StateRecord out.heap out.registers.d label
        ⟨weights,best,cost,total,(addLoads loads q.mask amount).1,⟨q,amount⟩::events⟩ := by
  obtain ⟨e₁,loadsRoot,l₁,r₁,loadRep⟩ := loads_return amount lrRep maskRep arRep context (by simp)
    next frame d dense ⟨lr,ctx,frame,d⟩ 4551 stack source
  rw [PackingLoadRow.result_eq_addLoads] at loadRep
  have call : tickNatural program (state heap next lr ctx frame d stack source 4550)=
      some ⟨state heap next lr ctx frame d (⟨4551,.r0,⟨lr,ctx,frame,d⟩⟩::stack) source 4352,[],0⟩ := by
    have slot : program 4550=.call 4352 4551 .r0 := rfl
    simp [tickNatural,state,slot]
  obtain ⟨e₂,l₂,r₂,rep⟩ := allocate_state label q weights best (addLoads loads q.mask amount).1 cost total amount events
    (path_extend qp e₁) (path_extend ap e₁) (path_extend ep e₁) (path_extend tp e₁)
    (path_extend cp e₁) (path_extend bp e₁) (path_extend wp e₁)
    (choice_extend qrRep e₁) (stored_extend arRep e₁) (PackingStart.events_extend erRep e₁)
    (list_extend wrRep e₁) (list_extend brRep e₁) (stored_extend crRep e₁) (stored_extend trRep e₁)
    loadRep (next+e₁.length) ctx d (by simp [List.length_append,dense]) stack source
  refine ⟨e₁++e₂,state (heap++e₁++e₂) (next+e₁.length+8) wr er
    (next+e₁.length) (next+e₁.length+7) stack source 4605,
    by simp [l₁,l₂],?_,?_,?_,rfl,rfl,rfl,rep⟩
  · convert NaturalRun.step call (run_append r₁ r₂) using 1
    rfl
  · simp [state,List.append_assoc]
  · simp [state,List.length_append,l₂,Nat.add_assoc]
end DirectedFlowCutGap.AdaptivePackingState
