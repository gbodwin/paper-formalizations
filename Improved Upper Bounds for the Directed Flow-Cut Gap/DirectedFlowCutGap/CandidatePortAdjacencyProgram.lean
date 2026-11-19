import DirectedFlowCutGap.CandidateLevelTestProgram
import DirectedFlowCutGap.CandidateCapacityFlags
import DirectedFlowCutGap.GraphAdjacencyProgram

/-!
# Physical adjacency of two tagged terminal ports

For an allowed pair of port kinds, the program reads the original stored
adjacency matrix. A source port can also reach the sink port with the same
vertex number. This extra case uses a binary comparison of the input labels.
-/

namespace DirectedFlowCutGap.CandidatePortAdjacencyProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)

inductive Kind where
  | core | start | finish
  deriving DecidableEq

inductive Route where
  | absent | original | diagonal
  deriving DecidableEq

def kind {n : ℕ} : TerminalPorts.Vertex (Fin n) → Kind
  | .inl _ => .core
  | .inr (.inl _) => .start
  | .inr (.inr _) => .finish

def vertex {n : ℕ} : TerminalPorts.Vertex (Fin n) → Fin n
  | .inl v | .inr (.inl v) | .inr (.inr v) => v

def tag : Kind → Cell ℕ
  | .core => .nil
  | .start => .flag false
  | .finish => .flag true

def route : Kind → Kind → Route
  | .core,.core | .core,.finish | .start,.core => .original
  | .start,.finish => .diagonal
  | _,_ => .absent

def rows {n : ℕ} (D : Input n) : List Bits := D.adjacency.toList.map Vector.toList

def edge {n : ℕ} (D : Input n) (u v : Fin n) : Bool := (D.adjacency[u.val])[v.val]

def result {n : ℕ} (D : Input n) (p q : TerminalPorts.Vertex (Fin n)) : Bool :=
  match route (kind p) (kind q) with
  | .absent => false
  | .original => edge D (vertex p) (vertex q)
  | .diagonal => decide (vertex p=vertex q) || edge D (vertex p) (vertex q)

theorem result_eq {n : ℕ} (D : Input n) (p q : TerminalPorts.Vertex (Fin n)) :
    result D p q = (D.portAdjWithCost p q).1 := by
  rcases p with p | (p | p) <;> rcases q with q | (q | q) <;> rfl

def graphLabel (pc : Fin 36) : Fin 116 := if pc.val=35 then 10 else ⟨32+pc.val,by omega⟩
def compareLabel (pc : Fin 48) : Fin 116 := if pc.val=47 then 26 else ⟨68+pc.val,by omega⟩

def program : Program 116 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .field .r3 .r2 false 1
    | 1 => .branch .r3 2 4 7 31
    | 2 => .field .r3 .r2 true 3
    | 3 => .branch .r3 8 7 8 31
    | 4 => .field .r3 .r2 true 5
    | 5 => .branch .r3 8 7 12 31
    | 7 => .make .r3 (.flag false) 10
    | 8 => .call (graphLabel 27) 10 .r3
    | 12 => .call 24 13 .r3
    | 13 => .branch .r3 15 8 8 31
    | 15 => .make .r3 (.flag true) 10
    | 24 => .field .r1 .r1 true 25
    | 25 => .call (compareLabel 0) 26 .r3
    | 26 => .ret .r3
    | _ => .halt
  else if h : pc.val<68 then ReferenceProgramLabels.instruction graphLabel
    (GraphAdjacencyProgram.program ⟨pc.val-32,by omega⟩)
  else ReferenceProgramLabels.instruction compareLabel
    (BinaryComparisonProgram.program ⟨pc.val-68,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 116))
    (tape : Bits) (pc : Fin 116) : NaturalState 116 := ⟨heap,heap.length,r,stack,pc,tape⟩

def routePC : Route → Fin 116
  | .absent => 7
  | .original => 8
  | .diagonal => 12

def routeSteps (a : Kind) : ℕ := if a=.finish then 2 else 4

def instructionBound (n P Q : ℕ) : ℕ := 12*n+26*(P+Q)+59

private theorem graph_slots (pc : Fin 36) (h : GraphAdjacencyProgram.program pc≠.halt) :
    program (graphLabel pc) =
      ReferenceProgramLabels.instruction graphLabel (GraphAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=35
  · have eq : pc=35 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,graphLabel,hp,show ¬32+pc.val<32 by omega,show 32+pc.val<68 by omega]

private theorem compare_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (compareLabel pc) =
      ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have eq : pc=47 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,compareLabel,hp,show ¬68+pc.val<32 by omega,show ¬68+pc.val<68 by omega]

set_option maxHeartbeats 1200000 in
private theorem dispatch {heap : NaturalHeap} {r : Registers ℕ} {p q : Kind} {first second : ℕ}
    (pair : heap[r.c]?=some (.pair first second)) (a : heap[first]?=some (tag p))
    (b : heap[second]?=some (tag q)) (tape : Bits) :
    NaturalRun program (routeSteps p) (state heap r [] tape 0) []
      (state heap (r.set .r3 (if p=.finish then first else second)) [] tape (routePC (route p q))) := by
  apply ReferenceProgramSteps.sound
  cases p <;> cases q <;>
    simp [ReferenceProgramSteps.run,program,state,routeSteps,routePC,route,tag,tickNatural,
      Registers.get,Registers.set,tagBranch, *]

section Calls
variable {n : ℕ} {D : Input n} {heap : NaturalHeap} {r : Registers ℕ}
variable {x y : Bits} {u v : Fin n}

private theorem read_edge (xRep : BoolList heap r.a x) (ctx : GraphAdjacencyProgram.Context heap r.b (rows D) y)
    (hx : value x=u.val) (hy : value y=v.val) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (edge D u v)) ∧
      NaturalRun program (GraphAdjacencyProgram.steps x y+1) (state heap r [] tape 8) []
        (state (heap++ext) (r.set .r3 root) [] tape 10) := by
  have rowIn : value x<(rows D).length := by simp [rows,hx]
  have colIn : value y<((rows D)[value x]).length := by simp [rows,hx,hy]
  obtain ⟨ext,root,_,body,rep⟩ := GraphAdjacencyProgram.read_return xRep ctx rowIn colIn heap.length
    r.c r.d rfl r 35 [] tape
  let frame : Frame ℕ 116 := ⟨10,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 8)=some ⟨state heap r [frame] tape (graphLabel 27),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run graphLabel GraphAdjacencyProgram.program program graph_slots body
  have run : NaturalRun program (GraphAdjacencyProgram.steps x y)
      (state heap r [frame] tape (graphLabel 27)) [] (state (heap++ext) (r.set .r3 root) [] tape 10) := by
    cases r
    simpa [state,frame,GraphAdjacencyProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,graphLabel,Registers.set] using lift
  refine ⟨ext,root,?_,.step enter run⟩
  simpa [rows,hx,hy,edge] using rep

private theorem compare_vertex (xRep : BoolList heap r.a x)
    (ctx : GraphAdjacencyProgram.Context heap r.b (rows D) y) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order x y)) ∧
      NaturalRun program (BinaryComparisonProgram.steps x y+4) (state heap r [] tape 12) []
        (state (heap++ext) (r.set .r3 root) [] tape 13) := by
  obtain ⟨matrix,right,pair,_,yRep⟩ := ctx
  let args := r.set .r1 right
  let outer : Frame ℕ 116 := ⟨13,.r3,r⟩
  let inner : Frame ℕ 116 := ⟨26,.r3,args⟩
  have setup : NaturalRun program 3 (state heap r [] tape 12) []
      (state heap args [inner,outer] tape (compareLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,args,outer,inner,compareLabel,tickNatural,Registers.get,pair]
  obtain ⟨ext,root,len,body,rep⟩ := BinaryComparisonProgram.compare_return (b:=args.b)
    xRep yRep heap.length args.c args.d rfl args 47 [] tape
  let stop := state (heap++ext) (args.set .r3 root) [outer] tape 26
  have lift := ReferenceProgramLabels.run compareLabel BinaryComparisonProgram.program program compare_slots body
  have lift := ReferenceProgramStack.run program [outer] lift
  have run : NaturalRun program (BinaryComparisonProgram.steps x y)
      (state heap args [inner,outer] tape (compareLabel 0)) [] stop := by
    cases r
    simpa [state,args,stop,inner,BinaryComparisonProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,compareLabel,Registers.set,len] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 13,[],0⟩ := by
    simp [stop,state,outer,program,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have trace := append_run setup (append_run run (.step ret (.done _)))
  have counted : 3+(BinaryComparisonProgram.steps x y+1)=BinaryComparisonProgram.steps x y+4 := by omega
  rw [← counted]
  exact trace

private theorem finish_flag (b : Bool) (tape : Bits) :
    NaturalRun program 1 (state heap r [] tape (if b then 15 else 7)) []
      (state (heap++[.flag b]) (r.set .r3 heap.length) [] tape 10) := by
  apply ReferenceProgramSteps.sound
  cases b <;> simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell]

end Calls

theorem natural_adjacency {n : ℕ} {D : Input n} {p q : TerminalPorts.Vertex (Fin n)}
    {heap : NaturalHeap} {r : Registers ℕ} {x y : Bits} {first second : ℕ}
    (left : BoolList heap r.a x) (context : GraphAdjacencyProgram.Context heap r.b (rows D) y)
    (hx : value x=(vertex p).val) (hy : value y=(vertex q).val)
    (pair : heap[r.c]?=some (.pair first second))
    (tagLeft : heap[first]?=some (tag (kind p))) (tagRight : heap[second]?=some (tag (kind q))) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      (heap++ext)[root]?=some (.flag (result D p q)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 10) ∧
      k ≤ instructionBound n x.length y.length := by
  let args := r.set .r3 (if kind p=.finish then first else second)
  have routeRun := dispatch pair tagLeft tagRight tape
  have routeBound : routeSteps (kind p)≤4 := by unfold routeSteps; split <;> decide
  have xbound : value x<n := by rw [hx]; exact (vertex p).isLt
  have ybound : value y<n := by rw [hy]; exact (vertex q).isLt
  have graph : GraphAdjacencyProgram.steps x y≤12*n+10*(x.length+y.length)+29 := by
    have a := BinaryPointerListRead.steps_bound x
    have b := BinaryPointerListRead.steps_bound y
    unfold GraphAdjacencyProgram.steps
    omega
  have comparison := BinaryComparisonProgram.steps_bound x y
  cases which : route (kind p) (kind q) with
  | absent =>
    refine ⟨[.flag false],args,heap.length,routeSteps (kind p)+1,?_,?_,?_⟩
    · simp [result,which]
    · have enter : NaturalRun program (routeSteps (kind p)) (state heap r [] tape 0) []
          (state heap args [] tape 7) := by simpa [args,which,routePC] using routeRun
      exact append_run enter (finish_flag false tape)
    · unfold instructionBound; omega
  | original =>
    have enter : NaturalRun program (routeSteps (kind p)) (state heap r [] tape 0) []
        (state heap args [] tape 8) := by simpa [args,which,routePC] using routeRun
    obtain ⟨ext,root,rep,run⟩ := read_edge (r:=args) left context hx hy tape
    refine ⟨ext,args,root,routeSteps (kind p)+(GraphAdjacencyProgram.steps x y+1),?_,append_run enter run,?_⟩
    · simpa [result,which] using rep
    · unfold instructionBound; omega
  | diagonal =>
    have enter : NaturalRun program (routeSteps (kind p)) (state heap r [] tape 0) []
        (state heap args [] tape 12) := by simpa [args,which,routePC] using routeRun
    obtain ⟨ec,cmp,tagRep,compare⟩ := compare_vertex (r:=args) left context tape
    let mid := heap++ec
    let saved := args.set .r3 cmp
    have branch : tickNatural program (state mid saved [] tape 13)=
        some ⟨state mid saved [] tape (if vertex p=vertex q then 15 else 8),[],0⟩ := by
      have equ : value x=value y ↔ vertex p=vertex q := by rw [hx,hy,Fin.ext_iff]
      rw [CandidateLevelTestProgram.order_eq_ite] at tagRep
      by_cases lt : value x<value y
      · have neq : ¬(vertex p=vertex q) := fun eq => lt.ne (equ.mpr eq)
        simp [state,program,tickNatural,Registers.get,Registers.set,tagBranch,mid,saved,lt,neq,tagRep,
          BinaryComparisonProgram.tag]
      · by_cases eq : vertex p=vertex q
        · have num := equ.mpr eq
          simp [state,program,tickNatural,Registers.get,Registers.set,tagBranch,mid,saved,eq,num,tagRep,
            BinaryComparisonProgram.tag]
        · have num := mt equ.mp eq
          simp [state,program,tickNatural,Registers.get,Registers.set,tagBranch,mid,saved,lt,eq,num,tagRep,
            BinaryComparisonProgram.tag]
    have lead := append_run enter compare
    by_cases eq : vertex p=vertex q
    · have select : tickNatural program (state mid saved [] tape 13)=some ⟨state mid saved [] tape 15,[],0⟩ := by
        simpa only [ite_eq_left eq] using branch
      let fresh := mid.length
      refine ⟨ec++[.flag true],saved,fresh,routeSteps (kind p)+(BinaryComparisonProgram.steps x y+4)+2,?_,?_,?_⟩
      · have stored : (mid++[.flag true])[fresh]?=some (.flag true) := by simp [fresh]
        simpa [mid,List.append_assoc,result,which,eq] using stored
      · have run := append_run lead (.step select (finish_flag true tape))
        simpa only [mid,fresh,List.append_assoc,List.nil_append,Nat.reduceAdd] using run
      · unfold instructionBound; omega
    · have select : tickNatural program (state mid saved [] tape 13)=some ⟨state mid saved [] tape 8,[],0⟩ := by
        simpa only [ite_eq_right eq] using branch
      obtain ⟨eg,root,rep,read⟩ := read_edge (r:=saved) (boolList_extend left ec)
        (GraphAdjacencyProgram.context_extend context ec) hx hy tape
      refine ⟨ec++eg,saved,root,routeSteps (kind p)+(BinaryComparisonProgram.steps x y+4)+
        (GraphAdjacencyProgram.steps x y+2),?_,?_,?_⟩
      · simpa [mid,List.append_assoc,result,which,eq] using rep
      · have run := append_run lead (.step select read)
        simpa only [mid,List.append_assoc,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using run
      · unfold instructionBound; omega

end DirectedFlowCutGap.CandidatePortAdjacencyProgram
