import DirectedFlowCutGap.BinaryLabelRangeProgram
import DirectedFlowCutGap.GraphWalkExtension

/-! Build the ordered Cartesian product of two stored word lists. -/

namespace DirectedFlowCutGap.WordPairProductProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open PathCostMaterialization (WordList list_extend)
open GraphWalkExtension (Edge EdgeList edgeList_extend)
open ConcreteExpressionProgram (append_run)

def program : Program 32 := fun pc => match pc.val with
  | 0 => .make .r2 .nil 1
  | 1 => .call 8 2 .r3
  | 8 => .branch .r0 9 31 31 10
  | 9 => .ret .r2
  | 10 => .field .r3 .r0 false 11
  | 11 => .field .r0 .r0 true 12
  | 12 => .call 8 13 .r2
  | 13 => .move .r0 .r3 14
  | 14 => .call 20 15 .r3
  | 15 => .ret .r3
  | 20 => .branch .r1 9 31 31 21
  | 21 => .field .r3 .r1 false 22
  | 22 => .field .r1 .r1 true 23
  | 23 => .call 20 24 .r2
  | 24 => .make .r3 (.pair .r0 .r3) 25
  | 25 => .make .r3 (.pair .r3 .r2) 15
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 := ⟨heap,heap.length,r,stack,pc,tape⟩

def rowSteps (columns : ℕ) : ℕ := 7*columns+2
def steps (rows columns : ℕ) : ℕ := rows*(7*columns+9)+4

private theorem row_return {heap : NaturalHeap} {r : Registers ℕ} {u : Bits}
    {vs : List Bits} {suffix : List (Bits×Bits)}
    (word : BoolList heap r.a u) (columns : WordList heap r.b vs) (tail : EdgeList heap r.c suffix)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,EdgeList (heap++ext) root (vs.map (fun v => (u,v))++suffix) ∧
      NaturalRun program (rowSteps vs.length) (state heap r (caller::stack) tape 20) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction vs generalizing heap r caller stack with
  | nil =>
    cases columns with
    | nil hp =>
      refine ⟨[],r.c,by simpa using tail,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,rowSteps,tickNatural,Registers.get,hp,tagBranch]
  | cons v vs ih =>
    cases columns with
    | @cons _ head rest _ _ hp hv hs =>
      let saved := caller::stack
      let args := (r.set .r3 head).set .r1 rest
      let recur : Frame ℕ 32 := ⟨24,.r2,args⟩
      have setup : NaturalRun program 4 (state heap r saved tape 20) [] (state heap args (recur::saved) tape 20) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,args,recur,hp]
      obtain ⟨ext,acc,rep,body⟩ := ih (r:=args) word hs tail recur saved
      let mid := heap++ext
      let i := mid.length
      let endCells : NaturalHeap := [.pair r.a head,.pair i acc]
      have finish : NaturalRun program 3 (state mid (args.set .r2 acc) saved tape 24) []
          (state (mid++endCells) (caller.saved.set caller.destination (i+1)) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
          Recipe.cell,i,endCells,args,saved,List.append_assoc,Nat.add_assoc]
      have top : (mid++endCells)[i+1]?=some (.pair i acc) := by
        rw [List.getElem?_append_right (show mid.length ≤ i+1 from Nat.le_succ _)]
        rw [show i+1-mid.length=1 by simp [i]]
        rfl
      have edge : Edge (mid++endCells) i (u,v) :=
        ⟨r.a,head,by simp [i,endCells],boolList_extend (boolList_extend word ext) endCells,
          boolList_extend (boolList_extend hv ext) endCells⟩
      have output : EdgeList (mid++endCells) (i+1) ((v::vs).map (fun v => (u,v))++suffix) :=
        .cons top edge (edgeList_extend rep endCells)
      refine ⟨ext++endCells,i+1,?_,?_⟩
      · simpa only [mid,List.append_assoc] using output
      · have run := append_run setup (append_run body finish)
        simp only [rowSteps] at run ⊢
        have counted : 4+(7*vs.length+2+3)=7*(v::vs).length+2 := by simp [Nat.mul_add]; omega
        rw [← counted]
        simpa [mid,List.append_assoc] using run

private theorem table_return {heap : NaturalHeap} {r : Registers ℕ} {us vs : List Bits} {suffix : List (Bits×Bits)}
    (rows : WordList heap r.a us) (columns : WordList heap r.b vs) (tail : EdgeList heap r.c suffix)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,EdgeList (heap++ext) root (us.product vs++suffix) ∧
      NaturalRun program (us.length*(7*vs.length+9)+2) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction us generalizing heap r caller stack with
  | nil =>
    cases rows with
    | nil hp =>
      refine ⟨[],r.c,by simpa [List.product] using tail,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,hp,tagBranch]
  | cons u us ih =>
    cases rows with
    | @cons _ head rest _ _ hp hu hs =>
      let saved := caller::stack
      let args := (r.set .r3 head).set .r0 rest
      let recur : Frame ℕ 32 := ⟨13,.r2,args⟩
      have setup : NaturalRun program 4 (state heap r saved tape 8) [] (state heap args (recur::saved) tape 8) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,args,recur,hp]
      obtain ⟨et,acc,rep,body⟩ := ih (r:=args) hs columns tail recur saved
      let mid := heap++et
      let withTail := args.set .r2 acc
      let row := withTail.set .r0 head
      let rowFrame : Frame ℕ 32 := ⟨15,.r3,row⟩
      have prepare : NaturalRun program 2 (state mid withTail saved tape 13) [] (state mid row (rowFrame::saved) tape 20) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,withTail,row,rowFrame]
      obtain ⟨er,root,full,rowRun⟩ := row_return (r:=row) (boolList_extend hu et) (list_extend columns et) rep rowFrame saved tape
      have ret : tickNatural program (state (mid++er) (row.set .r3 root) saved tape 15)=some
          ⟨state (mid++er) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,Registers.set,saved]
      refine ⟨et++er,root,?_,?_⟩
      · simpa only [List.product,List.flatMap_cons,List.append_assoc,mid] using full
      · have run := append_run setup (append_run body (append_run prepare (append_run rowRun (.step ret (.done _)))))
        rw [List.length_cons,Nat.succ_mul us.length (7*vs.length+9)]
        unfold rowSteps at run
        convert run using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]

theorem natural_product {heap : NaturalHeap} {r : Registers ℕ} {us vs : List Bits}
    (rows : WordList heap r.a us) (columns : WordList heap r.b vs) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),EdgeList (heap++ext) root (us.product vs) ∧
      NaturalRun program (steps us.length vs.length) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 2) := by
  let mid := heap++[.nil]
  let args := r.set .r2 heap.length
  let caller : Frame ℕ 32 := ⟨2,.r3,args⟩
  have setup : NaturalRun program 2 (state heap r [] tape 0) [] (state mid args [caller] tape 8) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell,mid,args,caller]
  have tail : EdgeList mid args.c [] := .nil (by simp [mid,args,Registers.set])
  obtain ⟨ext,root,rep,body⟩ := table_return (r:=args) (list_extend rows [.nil]) (list_extend columns [.nil]) tail caller [] tape
  refine ⟨[.nil]++ext,args,root,?_,?_⟩
  · simpa only [List.append_nil,List.append_assoc,mid] using rep
  · have run := append_run setup body
    unfold steps
    convert run using 1 <;> first | rfl | omega | simp only [caller,List.append_assoc]

end DirectedFlowCutGap.WordPairProductProgram
