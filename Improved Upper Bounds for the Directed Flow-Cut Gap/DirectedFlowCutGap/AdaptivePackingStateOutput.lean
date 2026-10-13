import DirectedFlowCutGap.AdaptivePackingWeightInput

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem allocate_state {n : ℕ} (label : Fin n → Bits) (q : BinaryFractionalCore.Choice n)
    (weights best loads : Row n) (cost total amount : Fraction) (events : List (BinaryFractionalCore.Event n))
    {heap : NaturalHeap} {frame qr ar er wr br cr tr lr : ℕ}
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
    (next b d : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=8 ∧ NaturalRun program 54
      (state heap next lr b frame d stack source 4551) []
      (state (heap++ext) (next+8) wr er next (next+7) stack source 4605) ∧
      PackingStart.StateRecord (heap++ext) (next+7) label
        ⟨weights,best,cost,total,loads,⟨q,amount⟩::events⟩ := by
  let e : NaturalHeap := [.pair lr frame,.pair qr ar,.pair (next+1) er,
    .pair lr (next+2),.pair tr (next+3),.pair cr (next+4),.pair br (next+5),.pair wr (next+6)]
  let h1 := heap++e.take 1
  let h2 := heap++e.take 2
  let h3 := heap++e.take 3
  let h4 := heap++e.take 4
  let h5 := heap++e.take 5
  let h6 := heap++e.take 6
  let h7 := heap++e.take 7
  let h8 := heap++e.take 8
  have root : h1[next]?=some (.pair lr frame) := by simp [h1,e,dense]
  have t4551 : tickNatural program (state heap next lr b frame d stack source 4551)=some ⟨(state h1 (next+1) lr b next d stack source 4552),[],0⟩ := by
    have slot : program 4551=.make .r2 (.pair .r0 .r2) 4552 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h1]
  have pair4552 : h1[next]?=some (.pair lr frame) := by simp [h1,e,dense]
  have path4552 : HeapPath h1 next [true,true,true,true,true,true,true,false] qr := .cons pair4552 (path_extend qp (e.take 1))
  have slots4552 : FieldSequence .r0 .r2 4552 [true,true,true,true,true,true,true,false] 4560 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))))
  have r4552 : NaturalRun program 8 (state h1 (next+1) lr b next d stack source 4552) [] (state h1 (next+1) qr b next d stack source 4560) := by
    have run := field_sequence_run (regs:=⟨lr,b,next,d⟩) slots4552 path4552 (next+1) stack source
    simpa [state,Registers.get,Registers.set] using run
  have pair4560 : h1[next]?=some (.pair lr frame) := by simp [h1,e,dense]
  have path4560 : HeapPath h1 next [true,true,true,true,true,true,false] ar := .cons pair4560 (path_extend ap (e.take 1))
  have slots4560 : FieldSequence .r1 .r2 4560 [true,true,true,true,true,true,false] 4567 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))))
  have r4560 : NaturalRun program 7 (state h1 (next+1) qr b next d stack source 4560) [] (state h1 (next+1) qr ar next d stack source 4567) := by
    have run := field_sequence_run (regs:=⟨qr,b,next,d⟩) slots4560 path4560 (next+1) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4567 : tickNatural program (state h1 (next+1) qr ar next d stack source 4567)=some ⟨(state h2 (next+2) (next+1) ar next d stack source 4568),[],0⟩ := by
    have slot : program 4567=.make .r0 (.pair .r0 .r1) 4568 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h1,h2,List.append_assoc,Nat.add_assoc]
  have pair4568 : h2[next]?=some (.pair lr frame) := by simp [h2,e,dense]
  have path4568 : HeapPath h2 next [true,true,true,true,true,true,true,true,true,false,true,true,true,true,true] er := .cons pair4568 (path_extend ep (e.take 2))
  have slots4568 : FieldSequence .r1 .r2 4568 [true,true,true,true,true,true,true,true,true,false,true,true,true,true,true] 4583 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))))))))))))
  have r4568 : NaturalRun program 15 (state h2 (next+2) (next+1) ar next d stack source 4568) [] (state h2 (next+2) (next+1) er next d stack source 4583) := by
    have run := field_sequence_run (regs:=⟨next+1,ar,next,d⟩) slots4568 path4568 (next+2) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4583 : tickNatural program (state h2 (next+2) (next+1) er next d stack source 4583)=some ⟨(state h3 (next+3) (next+1) er next (next+2) stack source 4584),[],0⟩ := by
    have slot : program 4583=.make .r3 (.pair .r0 .r1) 4584 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h2,h3,List.append_assoc,Nat.add_assoc]
  have pair4584 : h3[next]?=some (.pair lr frame) := by simp [h3,e,dense]
  have path4584 : HeapPath h3 next [false] lr := .cons pair4584 (.nil _)
  have slots4584 : FieldSequence .r0 .r2 4584 [false] 4585 := .cons rfl (.nil _)
  have r4584 : NaturalRun program 1 (state h3 (next+3) (next+1) er next (next+2) stack source 4584) [] (state h3 (next+3) lr er next (next+2) stack source 4585) := by
    have run := field_sequence_run (regs:=⟨next+1,er,next,next+2⟩) slots4584 path4584 (next+3) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4585 : tickNatural program (state h3 (next+3) lr er next (next+2) stack source 4585)=some ⟨(state h4 (next+4) lr er next (next+3) stack source 4586),[],0⟩ := by
    have slot : program 4585=.make .r3 (.pair .r0 .r3) 4586 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h3,h4,List.append_assoc,Nat.add_assoc]
  have pair4586 : h4[next]?=some (.pair lr frame) := by simp [h4,e,dense]
  have path4586 : HeapPath h4 next [true,false] tr := .cons pair4586 (path_extend tp (e.take 4))
  have slots4586 : FieldSequence .r0 .r2 4586 [true,false] 4588 := .cons rfl (.cons rfl (.nil _))
  have r4586 : NaturalRun program 2 (state h4 (next+4) lr er next (next+3) stack source 4586) [] (state h4 (next+4) tr er next (next+3) stack source 4588) := by
    have run := field_sequence_run (regs:=⟨lr,er,next,next+3⟩) slots4586 path4586 (next+4) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4588 : tickNatural program (state h4 (next+4) tr er next (next+3) stack source 4588)=some ⟨(state h5 (next+5) tr er next (next+4) stack source 4589),[],0⟩ := by
    have slot : program 4588=.make .r3 (.pair .r0 .r3) 4589 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h4,h5,List.append_assoc,Nat.add_assoc]
  have pair4589 : h5[next]?=some (.pair lr frame) := by simp [h5,e,dense]
  have path4589 : HeapPath h5 next [true,true,true,false,true] cr := .cons pair4589 (path_extend cp (e.take 5))
  have slots4589 : FieldSequence .r0 .r2 4589 [true,true,true,false,true] 4594 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))
  have r4589 : NaturalRun program 5 (state h5 (next+5) tr er next (next+4) stack source 4589) [] (state h5 (next+5) cr er next (next+4) stack source 4594) := by
    have run := field_sequence_run (regs:=⟨tr,er,next,next+4⟩) slots4589 path4589 (next+5) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4594 : tickNatural program (state h5 (next+5) cr er next (next+4) stack source 4594)=some ⟨(state h6 (next+6) cr er next (next+5) stack source 4595),[],0⟩ := by
    have slot : program 4594=.make .r3 (.pair .r0 .r3) 4595 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h5,h6,List.append_assoc,Nat.add_assoc]
  have pair4595 : h6[next]?=some (.pair lr frame) := by simp [h6,e,dense]
  have path4595 : HeapPath h6 next [true,true,true,false,false] br := .cons pair4595 (path_extend bp (e.take 6))
  have slots4595 : FieldSequence .r0 .r2 4595 [true,true,true,false,false] 4600 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))
  have r4595 : NaturalRun program 5 (state h6 (next+6) cr er next (next+5) stack source 4595) [] (state h6 (next+6) br er next (next+5) stack source 4600) := by
    have run := field_sequence_run (regs:=⟨cr,er,next,next+5⟩) slots4595 path4595 (next+6) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4600 : tickNatural program (state h6 (next+6) br er next (next+5) stack source 4600)=some ⟨(state h7 (next+7) br er next (next+6) stack source 4601),[],0⟩ := by
    have slot : program 4600=.make .r3 (.pair .r0 .r3) 4601 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h6,h7,List.append_assoc,Nat.add_assoc]
  have pair4601 : h7[next]?=some (.pair lr frame) := by simp [h7,e,dense]
  have path4601 : HeapPath h7 next [true,true,false] wr := .cons pair4601 (path_extend wp (e.take 7))
  have slots4601 : FieldSequence .r0 .r2 4601 [true,true,false] 4604 := .cons rfl (.cons rfl (.cons rfl (.nil _)))
  have r4601 : NaturalRun program 3 (state h7 (next+7) br er next (next+6) stack source 4601) [] (state h7 (next+7) wr er next (next+6) stack source 4604) := by
    have run := field_sequence_run (regs:=⟨br,er,next,next+6⟩) slots4601 path4601 (next+7) stack source
    simpa [state,Registers.get,Registers.set] using run
  have t4604 : tickNatural program (state h7 (next+7) wr er next (next+6) stack source 4604)=some ⟨(state h8 (next+8) wr er next (next+7) stack source 4605),[],0⟩ := by
    have slot : program 4604=.make .r3 (.pair .r0 .r3) 4605 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,e,h7,h8,List.append_assoc,Nat.add_assoc]
  refine ⟨e,rfl,?_,?_⟩
  · simpa [h8,e,List.append_assoc] using (run_append (.step t4551 (.done _)) (run_append r4552 (run_append r4560 (run_append (.step t4567 (.done _)) (run_append r4568 (run_append (.step t4583 (.done _)) (run_append r4584 (run_append (.step t4585 (.done _)) (run_append r4586 (run_append (.step t4588 (.done _)) (run_append r4589 (run_append (.step t4594 (.done _)) (run_append r4595 (run_append (.step t4600 (.done _)) (run_append r4601 (.step t4604 (.done _)))))))))))))))))
  · refine ⟨wr,br,cr,tr,lr,next+2,next+6,next+5,next+4,next+3,?_,?_,?_,?_,?_,
      list_extend wrRep e,list_extend brRep e,stored_extend crRep e,stored_extend trRep e,
      list_extend lrRep e,?_⟩
    · simp [e,dense]
    · simp [e,dense]
    · simp [e,dense]
    · simp [e,dense]
    · simp [e,dense]
    · apply PackingStart.EventList.cons (entry:=next+1) (choice:=qr) (amount:=ar) (tail:=er)
      · simp [e,dense]
      · simp [e,dense]
      · exact choice_extend qrRep e
      · exact stored_extend arRep e
      · exact PackingStart.events_extend erRep e
end DirectedFlowCutGap.AdaptivePackingState
