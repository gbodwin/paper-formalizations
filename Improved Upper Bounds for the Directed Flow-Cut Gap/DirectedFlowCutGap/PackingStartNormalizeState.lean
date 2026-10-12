import DirectedFlowCutGap.PackingStartFinalAllocation

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def initializedState {n : ℕ} (capacity y : Row n) (q : BinaryFractionalCore.Choice n) :
    BinaryFractionalCore.State n :=
  ⟨y,(normalized y q.mask).1,(objective capacity (normalized y q.mask).1).1,
    BinaryRational.zero,Vector.replicate n BinaryRational.zero,[]⟩

def finishSteps {n : ℕ} (capacity y : Row n) (q : BinaryFractionalCore.Choice n) : ℕ :=
  NormalizedRow.steps y.toList q.mask.toList+
    ObjectiveRow.steps capacity.toList (normalized y q.mask).1.toList+5*n+36

theorem normalize_state {n : ℕ} (label : Fin n → Bits) (capacity y : Row n) (q : BinaryFractionalCore.Choice n)
    {heap : NaturalHeap} {a b frame choice cap input yr : ℕ}
    (row : StoredList heap cap capacity.toList) (weights : StoredList heap yr y.toList)
    (saved : WeightFrame heap frame cap input yr) (selected : OracleChoice.StoredChoice heap choice label q)
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ ext out,NaturalRun program (finishSteps capacity y q)
      (state heap next a b frame choice [] source 3033) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=3057 ∧
      StateRecord out.heap out.registers.d label (initializedState capacity y q) := by
  obtain ⟨base,pairFrame,pairBase⟩ := saved
  obtain ⟨mask,bottleneck,pairChoice,flags,_⟩ := selected
  obtain ⟨en,rw,_,normRun,normRep⟩ := normalized_return weights flags (by simp) next frame choice dense
    ⟨yr,mask,frame,choice⟩ 3036 [] source
  let h1 := heap++en
  let n1 := next+en.length
  have dense1 : n1=h1.length := by simp [n1,h1,dense]
  let ef : NaturalHeap := [.pair rw frame]
  let h2 := h1++ef
  let n2 := n1+1
  have dense2 : n2=h2.length := by simp [n2,h2,ef,dense1]
  have best2 : StoredList h2 rw (normalized y q.mask).1.toList := by
    rw [←NormalizedRow.result_eq_normalized]
    exact list_extend normRep ef
  have cap2 := list_extend (list_extend row en) ef
  obtain ⟨ed,rd,_,objectiveRun,costRep⟩ := objective_return cap2 best2 (by simp) n2 n1 rw dense2
    ⟨cap,rw,n1,rw⟩ 3042 [] source
  let h3 := h2++ed
  let n3 := n2+ed.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  let eg : NaturalHeap := [.pair rd n1]
  let h4 := h3++eg
  let n4 := n3+1
  have dense4 : n4=h4.length := by simp [n4,h4,eg,dense3]
  have cap4 := list_extend (list_extend cap2 ed) eg
  have spine4 : IndexSpine h4 cap n := by simpa [h4,h3,h2,h1,List.append_assoc] using PackingZeroRow.stored_spine cap4
  obtain ⟨ez,rz,zr,lr,_,zeroRun,zeroPair,loads,zeroRep⟩ := zero_return spine4 n4 rw n3 rd dense4
    ⟨cap,rw,n3,rd⟩ 3044 [] source
  let h5 := h4++ez
  let n5 := n4+ez.length
  have dense5 : n5=h5.length := by simp [n5,h5,dense4]
  have newFrame : h2[n1]?=some (.pair rw frame) := by simp [h2,ef,dense1]
  have costFrame : h4[n3]?=some (.pair rd n1) := by simp [h4,eg,dense3]
  have frame2 : h2[frame]?=some (.pair yr base) := lookup_extend (lookup_extend pairFrame en) ef
  have base2 : h2[base]?=some (.pair cap input) := lookup_extend (lookup_extend pairBase en) ef
  have weights5 := list_extend (list_extend (list_extend (list_extend (list_extend weights en) ef) ed) eg) ez
  have best5 := list_extend (list_extend (list_extend best2 ed) eg) ez
  have cost5 : Stored h5 rd (objective capacity (normalized y q.mask).1).1 := by
    rw [←ObjectiveRow.result_eq_objective]
    exact stored_extend (stored_extend costRep eg) ez
  obtain ⟨ea,la,allocate,rep⟩ := final_allocation label y (normalized y q.mask).1
    (objective capacity (normalized y q.mask).1).1
    (lookup_extend costFrame ez) (lookup_extend (lookup_extend (lookup_extend newFrame ed) eg) ez)
    (lookup_extend (lookup_extend (lookup_extend frame2 ed) eg) ez) zeroPair
    weights5 best5 cost5 zeroRep loads n5 dense5 source
  have t3033 : tickNatural program (state heap next a b frame choice [] source 3033)=
      some ⟨state heap next a mask frame choice [] source 3034,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pairChoice]
  have t3034 : tickNatural program (state heap next a mask frame choice [] source 3034)=
      some ⟨state heap next yr mask frame choice [] source 3035,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pairFrame]
  have t3035 : tickNatural program (state heap next yr mask frame choice [] source 3035)=
      some ⟨state heap next yr mask frame choice [⟨3036,.r3,⟨yr,mask,frame,choice⟩⟩] source 2676,[],0⟩ := by
    simp [tickNatural,program,state]
  have t3036 : tickNatural program (state h1 n1 yr mask frame rw [] source 3036)=
      some ⟨state h2 n2 yr mask n1 rw [] source 3037,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,n2,ef]
  have t3037 : tickNatural program (state h2 n2 yr mask n1 rw [] source 3037)=
      some ⟨state h2 n2 yr rw n1 rw [] source 3038,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t3038 : tickNatural program (state h2 n2 yr rw n1 rw [] source 3038)=
      some ⟨state h2 n2 frame rw n1 rw [] source 3039,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,newFrame]
  have t3039 : tickNatural program (state h2 n2 frame rw n1 rw [] source 3039)=
      some ⟨state h2 n2 base rw n1 rw [] source 3040,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frame2]
  have t3040 : tickNatural program (state h2 n2 base rw n1 rw [] source 3040)=
      some ⟨state h2 n2 cap rw n1 rw [] source 3041,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,base2]
  have t3041 : tickNatural program (state h2 n2 cap rw n1 rw [] source 3041)=
      some ⟨state h2 n2 cap rw n1 rw [⟨3042,.r3,⟨cap,rw,n1,rw⟩⟩] source 2992,[],0⟩ := by
    simp [tickNatural,program,state]
  have t3042 : tickNatural program (state h3 n3 cap rw n1 rd [] source 3042)=
      some ⟨state h4 n4 cap rw n3 rd [] source 3043,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h4,n4,eg]
  have t3043 : tickNatural program (state h4 n4 cap rw n3 rd [] source 3043)=
      some ⟨state h4 n4 cap rw n3 rd [⟨3044,.r3,⟨cap,rw,n3,rd⟩⟩] source 3004,[],0⟩ := by
    simp [tickNatural,program,state]
  have last := NaturalRun.step t3042 (.step t3043 (run_append zeroRun allocate))
  have middle := NaturalRun.step t3036 (.step t3037 (.step t3038 (.step t3039 (.step t3040
    (.step t3041 (run_append objectiveRun last))))))
  have whole := NaturalRun.step t3033 (.step t3034 (.step t3035 (run_append normRun middle)))
  let ext := en++ef++ed++eg++ez++ea
  refine ⟨ext,state (h5++ea) (n5+6) yr (n5+4) frame (n5+5) [] source 3057,?_,?_,?_,rfl,rfl,rfl,rep⟩
  · convert whole using 1
    · unfold finishSteps;omega
    · rfl
  · simp [state,h5,h4,h3,h2,h1,ext,List.append_assoc]
  · simp [state,ext,n5,n4,n3,n2,n1,ef,eg,la];omega
end DirectedFlowCutGap.PackingStart
