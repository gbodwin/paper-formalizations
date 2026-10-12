import DirectedFlowCutGap.PackingStateRecord

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem final_allocation {n : ℕ} (label : Fin n → Bits) (y w : Row n) (cost : Fraction)
    {heap : NaturalHeap} {a b frame packed yr wr cr zr lr yf wf previous : ℕ}
    (f0 : heap[frame]?=some (.pair cr wf)) (f1 : heap[wf]?=some (.pair wr yf))
    (f2 : heap[yf]?=some (.pair yr previous)) (pair : heap[packed]?=some (.pair zr lr))
    (weights : StoredList heap yr y.toList) (best : StoredList heap wr w.toList)
    (objective : Stored heap cr cost) (zeroRep : Stored heap zr BinaryRational.zero)
    (loads : StoredList heap lr (List.replicate n BinaryRational.zero))
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ ext,ext.length=6 ∧ NaturalRun program 13
      (state heap next a b frame packed [] source 3044) []
      (state (heap++ext) (next+6) yr (next+4) yf (next+5) [] source 3057) ∧
      StateRecord (heap++ext) (next+5) label
        ⟨y,w,cost,BinaryRational.zero,Vector.replicate n BinaryRational.zero,[]⟩ := by
  let e : NaturalHeap := [.nil,.pair lr next,.pair zr (next+1),.pair cr (next+2),
    .pair wr (next+3),.pair yr (next+4)]
  let h1 := heap++[.nil]
  let h2 := h1++[.pair lr next]
  let h3 := h2++[.pair zr (next+1)]
  let h4 := h3++[.pair cr (next+2)]
  let h5 := h4++[.pair wr (next+3)]
  let h6 := h5++[.pair yr (next+4)]
  have t3044 : tickNatural program (state heap next a b frame packed [] source 3044)=
      some ⟨state h1 (next+1) next b frame packed [] source 3045,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h1]
  have lookup3045 : h1[packed]?=some (.pair zr lr) := by
    exact lookup_extend pair _
  have t3045 : tickNatural program (state h1 (next+1) next b frame packed [] source 3045)=
      some ⟨state h1 (next+1) next lr frame packed [] source 3046,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3045]
  have t3046 : tickNatural program (state h1 (next+1) next lr frame packed [] source 3046)=
      some ⟨state h2 (next+2) next (next+1) frame packed [] source 3047,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,Nat.add_assoc]
  have lookup3047 : h2[packed]?=some (.pair zr lr) := by
    apply lookup_extend
    exact lookup_extend pair _
  have t3047 : tickNatural program (state h2 (next+2) next (next+1) frame packed [] source 3047)=
      some ⟨state h2 (next+2) zr (next+1) frame packed [] source 3048,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3047]
  have t3048 : tickNatural program (state h2 (next+2) zr (next+1) frame packed [] source 3048)=
      some ⟨state h3 (next+3) zr (next+2) frame packed [] source 3049,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h3,Nat.add_assoc]
  have lookup3049 : h3[frame]?=some (.pair cr wf) := by
    apply lookup_extend
    apply lookup_extend
    exact lookup_extend f0 _
  have t3049 : tickNatural program (state h3 (next+3) zr (next+2) frame packed [] source 3049)=
      some ⟨state h3 (next+3) cr (next+2) frame packed [] source 3050,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3049]
  have t3050 : tickNatural program (state h3 (next+3) cr (next+2) frame packed [] source 3050)=
      some ⟨state h4 (next+4) cr (next+3) frame packed [] source 3051,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h4,Nat.add_assoc]
  have lookup3051 : h4[frame]?=some (.pair cr wf) := by
    apply lookup_extend
    apply lookup_extend
    apply lookup_extend
    exact lookup_extend f0 _
  have t3051 : tickNatural program (state h4 (next+4) cr (next+3) frame packed [] source 3051)=
      some ⟨state h4 (next+4) cr (next+3) wf packed [] source 3052,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3051]
  have lookup3052 : h4[wf]?=some (.pair wr yf) := by
    apply lookup_extend
    apply lookup_extend
    apply lookup_extend
    exact lookup_extend f1 _
  have t3052 : tickNatural program (state h4 (next+4) cr (next+3) wf packed [] source 3052)=
      some ⟨state h4 (next+4) wr (next+3) wf packed [] source 3053,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3052]
  have t3053 : tickNatural program (state h4 (next+4) wr (next+3) wf packed [] source 3053)=
      some ⟨state h5 (next+5) wr (next+4) wf packed [] source 3054,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h5,Nat.add_assoc]
  have lookup3054 : h5[wf]?=some (.pair wr yf) := by
    apply lookup_extend
    apply lookup_extend
    apply lookup_extend
    apply lookup_extend
    exact lookup_extend f1 _
  have t3054 : tickNatural program (state h5 (next+5) wr (next+4) wf packed [] source 3054)=
      some ⟨state h5 (next+5) wr (next+4) yf packed [] source 3055,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3054]
  have lookup3055 : h5[yf]?=some (.pair yr previous) := by
    apply lookup_extend
    apply lookup_extend
    apply lookup_extend
    apply lookup_extend
    exact lookup_extend f2 _
  have t3055 : tickNatural program (state h5 (next+5) wr (next+4) yf packed [] source 3055)=
      some ⟨state h5 (next+5) yr (next+4) yf packed [] source 3056,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup3055]
  have t3056 : tickNatural program (state h5 (next+5) yr (next+4) yf packed [] source 3056)=
      some ⟨state h6 (next+6) yr (next+4) yf (next+5) [] source 3057,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h6,Nat.add_assoc]
  have all := NaturalRun.step t3044 (.step t3045 (.step t3046 (.step t3047 (.step t3048 (.step t3049 (.step t3050 (.step t3051 (.step t3052 (.step t3053 (.step t3054 (.step t3055 (.step t3056 (.done _)))))))))))))
  have eh : heap++e=h6 := by simp [e,h6,h5,h4,h3,h2,h1,List.append_assoc]
  refine ⟨e,rfl,?_,?_⟩
  · simpa [eh] using all
  · refine ⟨yr,wr,cr,zr,lr,next,next+4,next+3,next+2,next+1,?_,?_,?_,?_,?_,
      list_extend weights e,list_extend best e,stored_extend objective e,stored_extend zeroRep e,?_,?_⟩
    · simp [e,dense]
    · simp [e,dense]
    · simp [e,dense]
    · simp [e,dense]
    · simp [e,dense]
    · simpa using list_extend loads e
    · exact .nil (by simp [e,dense])
end DirectedFlowCutGap.PackingStart
