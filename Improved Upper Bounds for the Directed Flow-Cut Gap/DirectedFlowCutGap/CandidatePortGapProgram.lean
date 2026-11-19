import DirectedFlowCutGap.CandidatePortAdjacencyProgram
import DirectedFlowCutGap.BinaryMinimumWordProgram

/-!
# Candidate port gap and active flag from stored removals

The program indexes the original removal mask for a core vertex. It
returns whether that vertex contributes signed unit costs and the binary
gap bound. Terminal ports contribute zero and have gap zero.
-/

namespace DirectedFlowCutGap.CandidatePortGapProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidatePortAdjacencyProgram (Kind kind tag vertex)

def active {n : ℕ} (D : Input n) : TerminalPorts.Vertex (Fin n) → Bool
  | .inl v => !D.removed[v.val]
  | .inr _ => false

def gap {n : ℕ} (D : Input n) (grid cap : Bits) : TerminalPorts.Vertex (Fin n) → Bits
  | .inl v => if D.removed[v.val] then grid else cap
  | .inr _ => []

theorem gap_value {n : ℕ} (D : Input n) (grid bound : Bits) (p : TerminalPorts.Vertex (Fin n)) :
    value (gap D grid (BinaryMinimumWordProgram.word grid bound) p)=
      min (value grid) (D.portCapacity (value grid) (value bound) p) := by
  cases p with
  | inl v => cases h : D.removed[v.val] <;> simp [gap,Input.portCapacity,h,BinaryMinimumWordProgram.word_value]
  | inr p => simp [gap,Input.portCapacity,value]

def InputBounds (heap : NaturalHeap) (root : ℕ) (grid cap : Bits) : Prop :=
  ∃ g c,heap[root]?=some (.pair g c) ∧ BoolList heap g grid ∧ BoolList heap c cap

def Stored (heap : NaturalHeap) (root : ℕ) (enabled : Bool) (word : Bits) : Prop :=
  ∃ f w,heap[root]?=some (.pair f w) ∧ heap[f]?=some (.flag enabled) ∧ BoolList heap w word

theorem bounds_extend {heap : NaturalHeap} {root : ℕ} {grid cap : Bits}
    (h : InputBounds heap root grid cap) (ext : NaturalHeap) : InputBounds (heap++ext) root grid cap := by
  obtain ⟨g,c,pair,gridRep,capRep⟩ := h
  exact ⟨g,c,lookup_extend pair ext,boolList_extend gridRep ext,boolList_extend capRep ext⟩

theorem stored_extend {heap : NaturalHeap} {root : ℕ} {enabled : Bool} {word : Bits}
    (h : Stored heap root enabled word) (ext : NaturalHeap) : Stored (heap++ext) root enabled word := by
  obtain ⟨f,w,pair,flag,rep⟩ := h
  exact ⟨f,w,lookup_extend pair ext,lookup_extend flag ext,boolList_extend rep ext⟩

def label (pc : Fin 36) : Fin 52 := if pc.val=35 then 2 else ⟨16+pc.val,by omega⟩

def program : Program 52 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .branch .r3 1 8 8 15
    | 1 => .call (label 25) 2 .r3
    | 2 => .branch .r3 15 3 5 15
    | 3 => .field .r2 .r2 true 4
    | 4 => .make .r3 (.flag true) 10
    | 5 => .field .r2 .r2 false 6
    | 6 => .make .r3 (.flag false) 10
    | 8 => .make .r2 .nil 9
    | 9 => .make .r3 (.flag false) 10
    | 10 => .make .r3 (.pair .r3 .r2) 11
    | _ => .halt
  else ReferenceProgramLabels.instruction label (GraphAdjacencyProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 52))
    (tape : Bits) (pc : Fin 52) : NaturalState 52 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (k : Kind) (word : Bits) : ℕ :=
  if k=.core then BinaryPointerListRead.steps word+8 else 4

theorem steps_le (k : Kind) (word : Bits) (n : ℕ) (h : value word<n) :
    steps k word ≤ 6*n+10*word.length+17 := by
  have h := BinaryPointerListRead.steps_bound word
  unfold steps
  split <;> omega

private theorem slots (pc : Fin 36) (h : GraphAdjacencyProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (GraphAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=35
  · have eq : pc=35 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,label,hp,show ¬16+pc.val<16 by omega]

private theorem read_mask {heap : NaturalHeap} {r : Registers ℕ} {word flags : Bits}
    (index : BoolList heap r.a word) (mask : BoolList heap r.b flags) (inside : value word<flags.length)
    (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag flags[value word]) ∧
      NaturalRun program (BinaryPointerListRead.steps word+3) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r3 root) [] tape 2) := by
  obtain ⟨rs,len,ptrs,rep⟩ := GraphAdjacencyProgram.boolList_pointers mask
  have inPtrs : value word<rs.length := by omega
  obtain ⟨ext,_,body⟩ := GraphAdjacencyProgram.pointer_return index ptrs inPtrs heap.length r.c r.d
    rfl r 35 [] tape
  let frame : Frame ℕ 52 := ⟨2,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [frame] tape (label 25),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run label GraphAdjacencyProgram.program program slots body
  have run : NaturalRun program (BinaryPointerListRead.steps word+2)
      (state heap r [frame] tape (label 25)) [] (state (heap++ext) (r.set .r3 rs[value word]) [] tape 2) := by
    cases r
    simpa [frame,state,GraphAdjacencyProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,label,Registers.set] using lift
  exact ⟨ext,rs[value word],lookup_extend (rep _ inside) ext,.step enter run⟩

private theorem core_output {heap : NaturalHeap} {r : Registers ℕ} {removed : Bool} {grid cap : Bits}
    (flag : heap[r.d]?=some (.flag removed)) (limits : InputBounds heap r.c grid cap) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Stored (heap++ext) root (!removed) (if removed then grid else cap) ∧
      NaturalRun program 4 (state heap r [] tape 2) [] (state (heap++ext) (args.set .r3 root) [] tape 11) := by
  obtain ⟨g,c,pair,gridRep,capRep⟩ := limits
  let ptr := if removed then g else c
  let i := heap.length
  let ext : NaturalHeap := [.flag (!removed),.pair i ptr]
  let args := r.set .r2 ptr
  refine ⟨ext,args,i+1,⟨i,ptr,?_,?_,?_⟩,?_⟩
  · rw [List.getElem?_append_right (show heap.length ≤ i+1 from Nat.le_succ _)]
    change ext[i+1-i]?=some (.pair i ptr)
    rw [show i+1-i=1 by omega]
    rfl
  · simp [i,ext]
  · apply boolList_extend
    cases removed <;> assumption
  · apply ReferenceProgramSteps.sound
    cases removed <;>
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
        allocateNatural,Recipe.cell,tagBranch,ptr,i,ext,args,flag,pair,List.append_assoc,Nat.add_assoc]

private theorem terminal_output {heap : NaturalHeap} {r : Registers ℕ} {p : Kind}
    (notCore : p≠.core) (h : heap[r.d]?=some (tag p)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Stored (heap++ext) root false [] ∧
      NaturalRun program 4 (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 11) := by
  let i := heap.length
  let ext : NaturalHeap := [.nil,.flag false,.pair (i+1) i]
  let args := r.set .r2 i
  refine ⟨ext,args,i+2,⟨i+1,i,?_,?_,.nil ?_⟩,?_⟩
  · rw [List.getElem?_append_right (show heap.length ≤ i+2 by change i ≤ i+2; omega)]
    change ext[i+2-i]?=some (.pair (i+1) i)
    rw [show i+2-i=2 by omega]
    rfl
  · rw [List.getElem?_append_right (show heap.length ≤ i+1 from Nat.le_succ _)]
    change ext[i+1-i]?=some (.flag false)
    rw [show i+1-i=1 by omega]
    rfl
  · simp [i,ext]
  · apply ReferenceProgramSteps.sound
    cases p <;>
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
        allocateNatural,Recipe.cell,tagBranch,tag,i,ext,args,h,List.append_assoc,Nat.add_assoc] at notCore ⊢

theorem natural_gap {n : ℕ} (D : Input n) (p : TerminalPorts.Vertex (Fin n))
    {heap : NaturalHeap} {r : Registers ℕ} {word grid cap : Bits}
    (index : BoolList heap r.a word) (hx : value word=(vertex p).val)
    (mask : BoolList heap r.b D.removed.toList) (limits : InputBounds heap r.c grid cap)
    (htag : heap[r.d]?=some (tag (kind p))) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Stored (heap++ext) root (active D p) (gap D grid cap p) ∧
      NaturalRun program (steps (kind p) word) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 11) := by
  rcases p with u | u
  · have inside : value word<D.removed.toList.length := by simp [hx,vertex]
    obtain ⟨em,pointer,rep,read⟩ := read_mask index mask inside tape
    let args := r.set .r3 pointer
    have flag : (heap++em)[args.d]?=some (.flag D.removed[u.val]) := by simpa [hx,vertex,args,Registers.set] using rep
    obtain ⟨eo,regs,root,stored,finish⟩ := core_output flag (bounds_extend limits em) tape
    have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [] tape 1,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,htag,kind,tag,tagBranch]
    refine ⟨em++eo,regs,root,?_,?_⟩
    · simpa only [List.append_assoc,active,gap] using stored
    · have run := NaturalRun.step enter (append_run read finish)
      simpa only [steps,kind,ite_true,List.append_assoc,List.nil_append,Nat.add_assoc,
        Nat.reduceAdd] using run
  · have notCore : kind (.inr u)≠.core := by cases u <;> simp [kind]
    obtain ⟨ext,args,root,rep,run⟩ := terminal_output notCore htag tape
    refine ⟨ext,args,root,rep,?_⟩
    simpa only [steps,ite_eq_right notCore] using run

end DirectedFlowCutGap.CandidatePortGapProgram
