import DirectedFlowCutGap.PositiveInventoryBranches

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem inventory_return (rows : List Fraction) (words : List Bits) (aligned : words.length=rows.length)
    {heap : NaturalHeap} {a b : ℕ} (verts : GraphDiscoveryProgram.Vertices heap a words)
    (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 48)
    (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root,ext.length=cells rows ∧
      NaturalRun program (steps rows)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Inventory (heap++ext) root (selected (words.zip rows)) := by
  induction rows generalizing words heap a b next c d saved pc stack with
  | nil =>
    have hw : words=[] := by simpa using aligned
    subst words
    cases verts with
    | nil hp =>
      refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
      have t10 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t11 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11)=
          some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 12,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have t12 : tickNatural program
          (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 12)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact .step t10 (.step t11 (.step t12 (.done _)))
  | cons q qs ih =>
    cases words with
    | nil => simp at aligned
    | cons w ws =>
      have hal : ws.length=qs.length := by simpa using aligned
      cases verts with
      | @cons a vh vt w ws ha hw ht =>
        simp only [IndexedRationalRead.fields,List.map_cons] at table
        cases table with
        | @cons b cost ct num den _ _ _ hb hc hnum hden hct =>
          let pre : NaturalHeap := [.pair a b,.flag (BinaryArithmetic.isZero q.num).1]
          let h0 := heap++pre
          let frame : Frame ℕ 48 := ⟨pc,.r3,saved⟩
          have hp := numerator_prefix ha hb hc hnum next c d hn (frame::stack) source
          have hs : h0[next]?=some (.pair a b) := by simp [h0,pre,hn]
          have hf : h0[next+1]?=some (.flag (BinaryArithmetic.isZero q.num).1) := by simp [h0,pre,hn]
          have ha0 := lookup_extend ha pre
          have hb0 := lookup_extend hb pre
          have hv0 := GraphDiscoveryProgram.vertices_extend ht pre
          have hc0 := BinaryIndexedPairRead.table_extend hct pre
          by_cases hz : (BinaryArithmetic.isZero q.num).1=true
          · have adv := zero_advance hs ha0 hb0 (by simpa [hz] using hf)
              (next+2) num (frame::stack) source
            obtain ⟨ext,out,len,run,rep⟩ := ih ws hal hv0 hc0 (next+2) next (next+1)
              (by simp [pre,hn]) ⟨vt,ct,next,next+1⟩ 25 (frame::stack)
            have call : tickNatural program (state h0 (next+2) vt ct next (next+1) (frame::stack) source 24)=
                some ⟨state h0 (next+2) vt ct next (next+1)
                  (⟨25,.r3,⟨vt,ct,next,next+1⟩⟩::frame::stack) source 10,[],0⟩ := by rfl
            have ret : tickNatural program
                (state (h0++ext) (next+2+ext.length) vt ct next out (frame::stack) source 25)=
                some ⟨state (h0++ext) (next+2+ext.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
              simp [tickNatural,program,state,frame,Registers.get,Registers.set]
            refine ⟨pre++ext,out,?_,?_,?_⟩
            · simp [pre,cells,hz,len];omega
            · have whole := run_append hp (run_append adv (.step call (run_append run (.step ret (.done _)))))
              convert whole using 1 <;> simp [steps,hz,state,h0,pre,List.append_assoc,Nat.add_assoc] <;> omega
            · simpa [selected,hz,h0,List.zip_cons_cons,List.append_assoc] using rep
          · have hz' : (BinaryArithmetic.isZero q.num).1=false := Bool.eq_false_iff.mpr hz
            let item : Cell ℕ := .pair cost vh
            let h1 := h0++[item]
            have adv := positive_advance hs ha0 hb0 (by simpa [hz'] using hf)
              (next+2) num (frame::stack) source
            have hv1 := GraphDiscoveryProgram.vertices_extend hv0 [item]
            have hc1 := BinaryIndexedPairRead.table_extend hc0 [item]
            obtain ⟨ext,out,len,run,rep⟩ := ih ws hal hv1 hc1 (next+3) (next+2) (next+2)
              (by simp [pre,hn]) ⟨vt,ct,next+2,next+2⟩ 41 (frame::stack)
            have call : tickNatural program
                (state h1 (next+3) vt ct (next+2) (next+2) (frame::stack) source 40)=
                some ⟨state h1 (next+3) vt ct (next+2) (next+2)
                  (⟨41,.r3,⟨vt,ct,next+2,next+2⟩⟩::frame::stack) source 10,[],0⟩ := by rfl
            let last : Cell ℕ := .pair (next+2) out
            have alloc : tickNatural program
                (state (h1++ext) (next+3+ext.length) vt ct (next+2) out (frame::stack) source 41)=
                some ⟨state ((h1++ext)++[last]) (next+3+ext.length+1) vt ct (next+2)
                  (next+3+ext.length) (frame::stack) source 42,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,last]
            have ret : tickNatural program
                (state ((h1++ext)++[last]) (next+3+ext.length+1) vt ct (next+2)
                  (next+3+ext.length) (frame::stack) source 42)=
                some ⟨state ((h1++ext)++[last]) (next+3+ext.length+1) saved.a saved.b saved.c
                  (next+3+ext.length) stack source pc,[],0⟩ := by
              simp [tickNatural,program,state,frame,Registers.get,Registers.set]
            refine ⟨pre++[item]++ext++[last],next+3+ext.length,?_,?_,?_⟩
            · simp [pre,cells,hz',len];omega
            · have adv' : NaturalRun program 11
                  (state h0 (next+2) num b next (next+1) (frame::stack) source 18) []
                  (state h1 (next+3) vt ct (next+2) (next+2) (frame::stack) source 40) := by
                simpa [h1,item,Nat.add_assoc] using adv
              have whole := run_append hp (run_append adv' (.step call
                (run_append run (.step alloc (.step ret (.done _))))))
              convert whole using 1 <;> simp [steps,hz',state,h1,h0,pre,item,last,List.append_assoc,Nat.add_assoc] <;> omega
            · have hi : ((h1++ext)++[last])[next+2]?=some item :=
                lookup_extend (lookup_extend (by simp [h1,h0,pre,hn]) ext) [last]
              have hl : ((h1++ext)++[last])[next+3+ext.length]?=some last := by
                have hlen : (h1++ext).length=next+3+ext.length := by simp [h1,h0,pre,hn];omega
                rw [←hlen];simp
              have hq : RationalComparisonProgram.Stored heap cost q := ⟨num,den,hc,hnum,hden⟩
              have hq' := RationalComparisonProgram.stored_extend hq (pre++[item]++ext++[last])
              have hw' := boolList_extend hw (pre++[item]++ext++[last])
              have tail := inventory_extend rep [last]
              have cons := Inventory.cons hl hi
                (by simpa [h1,h0,List.append_assoc] using hq')
                (by simpa [h1,h0,List.append_assoc] using hw') tail
              simpa [selected,hz',h1,h0,item,last,List.zip_cons_cons,List.append_assoc] using cons
end DirectedFlowCutGap.PositiveInventory
