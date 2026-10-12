import DirectedFlowCutGap.OracleChoiceCapacity

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

def instructionBound {n : ℕ} (q : Option (BinaryFractionalGraphOracle.Selected n)) (W : ℕ) : ℕ :=
  OracleMask.instructionBound n ((q.map fun x => x.path.edges.length).getD 0) W+
    CapacityBottleneck.instructionBound n W+6*n+30

/-- Actual postprocessing of the retained selected record. The mask, capacity
query and both default branches execute in the same immutable heap trace. -/
theorem choice_return {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (capacity : Row n) (hn : 0<n) {heap : NaturalHeap} {a b : ℕ}
    {q : Option (BinaryFractionalGraphOracle.Selected n)}
    (selected : DemandCollection.SelectedOrigin heap a label q)
    (context : CapacityBottleneck.GraphContext heap b label capacity)
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ steps ext root,NaturalRun program steps
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 410) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredChoice (heap++ext) root label (choice capacity hn q) ∧
      ∀ W,(∀ i,(label i).length≤W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ instructionBound q W := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨vertices,table,hb,hv,ht⟩ := context
    have ctx : CapacityBottleneck.GraphContext heap b label capacity := ⟨vertices,table,hb,hv,ht⟩
    have enum : (List.finRange (n+1)).map label=label 0::((List.finRange n).map Fin.succ).map label := by
      rw [List.finRange_succ,List.map_cons]
    have headInput := hv
    rw [enum] at headInput
    cases headInput with
    | @cons _ zeroRoot tail _ vs hhead hzero htail =>
      cases q with
      | none =>
        obtain ⟨ext,root,maskRoot,wordRoot,_,run,hpair,hmask,hword⟩ := empty_choice_return selected hb
          (by rw [enum] at hv;exact hv) next c d dense saved pc stack source
        refine ⟨_,ext,root,run,?_,?_⟩
        · refine ⟨maskRoot,wordRoot,hpair,?_,hword⟩
          change BoolList (heap++ext) maskRoot (BinaryFractionalGraphOracle.singletonMask (0 : Fin (n+1))).1.toList
          rw [singleton_mask_list]
          simpa using hmask
        · intro W _ _
          simp only [List.length_map,List.length_finRange]
          unfold instructionBound
          omega
      | some q =>
        obtain ⟨z,ha,hz,encoded,hd,originalTail,ho⟩ := selected
        subst a
        let frames := (⟨pc,.r3,saved⟩::stack)
        obtain ⟨em,rm,lm,maskRun,maskStored,frame⟩ := selected_mask_run hz hd ho hb hv next c d dense frames source
        let mask := (BinaryFractionalGraphOracle.internalMask q.demand.1 q.demand.2 q.path.edges).1
        have masked : OracleMask.mask z.demand.sourceWord z.demand.targetWord z.path.edges
            ((List.finRange (n+1)).map label)=mask.toList := by
          rw [encoded.1.1,encoded.1.2,encoded.2.1]
          exact OracleMask.mask_encode label hlabel q.demand.1 q.demand.2 q.path.edges
        have actualMask : BoolList (heap++em) rm mask.toList := by simpa only [masked] using maskStored
        have dense1 : next+em.length=(heap++em).length := by simp [dense]
        obtain ⟨xs,ec,rc,exs,lc,capRun,result⟩ := choice_capacity_return label capacity mask (0 : Fin (n+1)) (a:=vertices) (b:=next+1) frame
          (graph_context_extend ctx em) (lookup_extend hb em) (lookup_extend hhead em)
          (boolList_extend hzero em) actualMask (next+em.length) dense1 saved pc stack source
        let ext : NaturalHeap := em++ec
        refine ⟨(OracleMask.steps z.demand.sourceWord z.demand.targetWord z.path.edges ((List.finRange (n+1)).map label)+13)+(CapacityBottleneck.selectedSteps (next+em.length+1) xs+finishSteps (BinaryFractionalGraphOracle.bottleneck capacity mask).1+5),ext,rc,?_,?_,?_⟩
        · simpa [ext,state,List.append_assoc,Nat.add_assoc,frames] using run_append maskRun capRun
        · simpa [ext,choice,mask,List.append_assoc] using result
        · intro W labels capacities
          have se : z.demand.sourceWord.length≤W := by rw [encoded.1.1];exact labels _
          have te : z.demand.targetWord.length≤W := by rw [encoded.1.2];exact labels _
          have ew : OracleMask.widths W z.path.edges := by
            rw [encoded.2.1]
            intro e he
            obtain ⟨e',_,rfl⟩ := List.mem_map.mp he
            exact labels _
          have vw : ∀ v∈(List.finRange (n+1)).map label,v.length≤W := by
            intro v hv
            obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
            exact labels i
          have mb := OracleMask.steps_le se te ew vw
          have cb := CapacityBottleneck.selected_steps_le xs (next+em.length+1) W
            (CapacityBottleneck.encoded_widths exs capacities)
          have xl : xs.length=n+1 := by simpa using exs.length_eq
          have el : z.path.edges.length=q.path.edges.length := by simp [encoded.2.1,GraphRelaxationRefinement.encode]
          have fb : finishSteps (BinaryFractionalGraphOracle.bottleneck capacity mask).1≤8 := by
            cases (BinaryFractionalGraphOracle.bottleneck capacity mask).1 <;> simp [finishSteps]
          simp only [List.length_map,List.length_finRange,el] at mb
          rw [xl] at cb
          simp only [instructionBound,Option.map_some,Option.getD_some]
          omega

end DirectedFlowCutGap.OracleChoice
