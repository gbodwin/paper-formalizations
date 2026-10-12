import DirectedFlowCutGap.PackingEntryConstants

namespace DirectedFlowCutGap.PackingEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem entry_high (ci amount y : Fraction) {heap : NaturalHeap} {a b c : ℕ}
    (cap : Stored heap a ci) (amountRep : Stored heap b amount) (weight : Stored heap c y)
    (next d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext factorRoot root,ext.length=cells ci amount y ∧
      NaturalRun program (steps ci amount y) (state heap next a b c d [] source 440) []
        (state (heap++ext) (next+ext.length) c factorRoot (next+9) root [] source 467) ∧
      Stored (heap++ext) root (result ci amount y) := by
  let e0 := constants next a b c
  let h0 := heap++e0
  let n0 := next+10
  have dense0 : n0=h0.length := by simp [n0,h0,e0,constants,hn]
  obtain ⟨oneRep,twoRep⟩ := constants_rep heap next a b c hn
  obtain ⟨ep,rp,lp,productRun,productRep⟩ := product_return two ci twoRep (stored_extend cap e0)
    n0 (next+9) (next+4) dense0 ⟨next+8,a,next+9,next+4⟩ 454 [] source
  let h1 := h0++ep
  let n1 := n0+ep.length
  have dense1 : n1=h1.length := by simp [n1,h1,dense0]
  obtain ⟨eq,rq,lq,quotientRun,quotientRep⟩ := quotient_return amount (doubled ci)
    (stored_extend (stored_extend amountRep e0) ep) productRep n1 (next+9) rp dense1
    ⟨b,rp,next+9,rp⟩ 459 [] source
  let h2 := h1++eq
  let n2 := n1+eq.length
  have dense2 : n2=h2.length := by simp [n2,h2,dense1]
  obtain ⟨ea,ra,la,additionRun,additionRep⟩ := addition_return one (quotient ci amount)
    (stored_extend (stored_extend oneRep ep) eq) quotientRep n2 (next+9) rq dense2
    ⟨next+5,rq,next+9,rq⟩ 462 [] source
  let h3 := h2++ea
  let n3 := n2+ea.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  obtain ⟨em,rm,lm,finishRun,finishRep⟩ := product_return y (factor ci amount)
    (stored_extend (stored_extend (stored_extend (stored_extend weight e0) ep) eq) ea)
    additionRep n3 (next+9) ra dense3 ⟨c,ra,next+9,ra⟩ 467 [] source
  have ctx0 : h0[next+9]?=some (.pair (next+5) (next+1)) := by simp [h0,e0,constants,hn]
  have frame0 : h0[next+1]?=some (.pair a next) := by simp [h0,e0,constants,hn]
  have args0 : h0[next]?=some (.pair b c) := by simp [h0,e0,constants,hn]
  have ctx1 := lookup_extend ctx0 ep
  have frame1 := lookup_extend frame0 ep
  have args1 := lookup_extend args0 ep
  have ctx2 := lookup_extend ctx1 eq
  have ctx3 := lookup_extend ctx2 ea
  have frame3 := lookup_extend (lookup_extend frame1 eq) ea
  have args3 := lookup_extend (lookup_extend args1 eq) ea
  simp only [List.append_assoc] at ctx2 ctx3 frame3 args3
  have t453 : tickNatural program (state h0 n0 (next+8) a (next+9) (next+4) [] source 453)=
      some ⟨state h0 n0 (next+8) a (next+9) (next+4) [⟨454,.r3,⟨next+8,a,next+9,next+4⟩⟩] source 130,[],0⟩ := by
    simp [tickNatural,program,state]
  have t454 : tickNatural program (state h1 n1 (next+8) a (next+9) rp [] source 454)=
      some ⟨state h1 n1 (next+8) rp (next+9) rp [] source 455,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t455 : tickNatural program (state h1 n1 (next+8) rp (next+9) rp [] source 455)=
      some ⟨state h1 n1 (next+1) rp (next+9) rp [] source 456,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ctx1,h1]
  have t456 : tickNatural program (state h1 n1 (next+1) rp (next+9) rp [] source 456)=
      some ⟨state h1 n1 next rp (next+9) rp [] source 457,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frame1,h1]
  have t457 : tickNatural program (state h1 n1 next rp (next+9) rp [] source 457)=
      some ⟨state h1 n1 b rp (next+9) rp [] source 458,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,args1,h1]
  have t458 : tickNatural program (state h1 n1 b rp (next+9) rp [] source 458)=
      some ⟨state h1 n1 b rp (next+9) rp [⟨459,.r3,⟨b,rp,next+9,rp⟩⟩] source 293,[],0⟩ := by
    simp [tickNatural,program,state]
  have t459 : tickNatural program (state h2 n2 b rp (next+9) rq [] source 459)=
      some ⟨state h2 n2 b rq (next+9) rq [] source 460,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t460 : tickNatural program (state h2 n2 b rq (next+9) rq [] source 460)=
      some ⟨state h2 n2 (next+5) rq (next+9) rq [] source 461,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ctx2,h2,h1]
  have t461 : tickNatural program (state h2 n2 (next+5) rq (next+9) rq [] source 461)=
      some ⟨state h2 n2 (next+5) rq (next+9) rq [⟨462,.r3,⟨next+5,rq,next+9,rq⟩⟩] source 436,[],0⟩ := by
    simp [tickNatural,program,state]
  have t462 : tickNatural program (state h3 n3 (next+5) rq (next+9) ra [] source 462)=
      some ⟨state h3 n3 (next+5) ra (next+9) ra [] source 463,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t463 : tickNatural program (state h3 n3 (next+5) ra (next+9) ra [] source 463)=
      some ⟨state h3 n3 (next+1) ra (next+9) ra [] source 464,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ctx3,h3,h2,h1]
  have t464 : tickNatural program (state h3 n3 (next+1) ra (next+9) ra [] source 464)=
      some ⟨state h3 n3 next ra (next+9) ra [] source 465,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frame3,h3,h2,h1]
  have t465 : tickNatural program (state h3 n3 next ra (next+9) ra [] source 465)=
      some ⟨state h3 n3 c ra (next+9) ra [] source 466,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,args3,h3,h2,h1]
  have t466 : tickNatural program (state h3 n3 c ra (next+9) ra [] source 466)=
      some ⟨state h3 n3 c ra (next+9) ra [⟨467,.r3,⟨c,ra,next+9,ra⟩⟩] source 130,[],0⟩ := by
    simp [tickNatural,program,state]
  have tailRun := NaturalRun.step t462 (.step t463 (.step t464 (.step t465 (.step t466 finishRun))))
  have mid2 := NaturalRun.step t459 (.step t460 (.step t461 (run_append additionRun tailRun)))
  have mid1 := NaturalRun.step t454 (.step t455 (.step t456 (.step t457 (.step t458 (run_append quotientRun mid2)))))
  have whole := run_append (constants_run heap next a b c d hn source)
    (.step t453 (run_append productRun mid1))
  let ext := e0++ep++eq++ea++em
  have heaps : heap++ext=h3++em := by simp [ext,h3,h2,h1,h0,List.append_assoc]
  have sizes : next+ext.length=n3+em.length := by simp [ext,n3,n2,n1,n0,e0,constants];omega
  refine ⟨ext,ra,rm,?_,?_,?_⟩
  · simp [ext,cells,lp,lq,la,lm,e0,constants];omega
  · rw [heaps,sizes]
    convert whole using 1
    · simp only [steps];omega
    · rfl
  · rw [heaps];exact finishRep
end DirectedFlowCutGap.PackingEntry
