import DirectedFlowCutGap.PathCostMaterialization

/-! A graph relaxation constructs the actual new directed edge-list and its
canonical sum by calling the real source-zero row access and arithmetic. -/
namespace DirectedFlowCutGap.GraphWalkExtension
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

structure Walk where
  edges : List (Bits×Bits)
  cost : Fraction

def Edge (heap : NaturalHeap) (root : ℕ) (e : Bits×Bits) : Prop :=
  ∃ u v,heap[root]?=some (.pair u v) ∧ BoolList heap u e.1 ∧ BoolList heap v e.2
inductive EdgeList (heap : NaturalHeap) : ℕ → List (Bits×Bits) → Prop
  | nil {p} : heap[p]?=some .nil → EdgeList heap p []
  | cons {p head tail e es} : heap[p]?=some (.pair head tail) →
      Edge heap head e → EdgeList heap tail es → EdgeList heap p (e::es)
def StoredWalk (heap : NaturalHeap) (p : ℕ) (q : Walk) : Prop :=
  ∃ es cost,heap[p]?=some (.pair es cost) ∧ EdgeList heap es q.edges ∧ Stored heap cost q.cost

theorem edge_extend {heap : NaturalHeap} {p : ℕ} {e : Bits×Bits} (h : Edge heap p e)
    (extra : NaturalHeap) : Edge (heap++extra) p e := by
  obtain ⟨u,v,hp,hu,hv⟩ := h
  exact ⟨u,v,lookup_extend hp extra,boolList_extend hu extra,boolList_extend hv extra⟩
theorem edgeList_extend {heap : NaturalHeap} {p : ℕ} {es : List (Bits×Bits)}
    (h : EdgeList heap p es) (extra : NaturalHeap) : EdgeList (heap++extra) p es := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp extra)
  | cons hp he _ ih => exact .cons (lookup_extend hp extra) (edge_extend he extra) ih
theorem walk_extend {heap : NaturalHeap} {p : ℕ} {q : Walk}
    (h : StoredWalk heap p q) (extra : NaturalHeap) : StoredWalk (heap++extra) p q := by
  obtain ⟨es,cost,hp,he,hc⟩ := h
  exact ⟨es,cost,lookup_extend hp extra,edgeList_extend he extra,stored_extend hc extra⟩

def result (rows : List Fraction) (sw : Bits) (e : Bits×Bits) (q : Walk) : Walk :=
  ⟨e::q.edges,(BinaryRational.add (OutgoingCostProgram.result rows sw e.1) q.cost).1⟩
def steps (rows : List Fraction) (sw : Bits) (e : Bits×Bits) (q : Walk) : ℕ :=
  OutgoingCostProgram.instructions sw e.1+
    CanonicalRationalAddition.instructions (OutgoingCostProgram.result rows sw e.1) q.cost+19

def cells (rows : List Fraction) (sw : Bits) (e : Bits×Bits) (q : Walk) : ℕ :=
  OutgoingCostProgram.cells sw e.1+
    CanonicalRationalAddition.cells (OutgoingCostProgram.result rows sw e.1) q.cost+3

def outLabel (pc : Fin 111) : Fin 270 := ⟨pc.val,by omega⟩
def addLabel (pc : Fin 142) : Fin 270 := ⟨pc.val+111,by omega⟩
def program : Program 270 := fun pc =>
  if pc.val=110 then .ret .r3
  else if pc.val=252 then .ret .r3
  else if h : pc.val<111 then
    ReferenceProgramLabels.instruction outLabel (OutgoingCostProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<253 then
    ReferenceProgramLabels.instruction addLabel (CanonicalRationalAddition.program ⟨pc.val-111,by omega⟩)
  else match pc.val with
  | 253 => .make .r3 (.pair .r0 .r1) 254
  | 254 => .move .r1 .r2 255
  | 255 => .move .r2 .r3 256
  | 256 => .field .r0 .r0 false 257
  | 257 => .call 109 258 .r3
  | 258 => .field .r1 .r2 true 259
  | 259 => .field .r1 .r1 true 260
  | 260 => .move .r0 .r3 261
  | 261 => .call 251 262 .r3
  | 262 => .field .r0 .r2 false 263
  | 263 => .field .r1 .r2 true 264
  | 264 => .field .r1 .r1 false 265
  | 265 => .make .r1 (.pair .r0 .r1) 266
  | 266 => .make .r3 (.pair .r1 .r3) 267
  | 267 => .ret .r3
  | 268 => .call 253 269 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 270)) (source : Bits) (pc : Fin 270) : NaturalState 270 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem out_slots (pc : Fin 111) (h : OutgoingCostProgram.program pc≠.halt) :
    program (outLabel pc)=ReferenceProgramLabels.instruction outLabel (OutgoingCostProgram.program pc) := by
  by_cases hp : pc.val=110
  · have he : pc=110 := Fin.ext hp
    subst pc;simp [OutgoingCostProgram.program] at h
  · simp [program,outLabel,pc.isLt,hp,show ¬pc.val=252 by omega]
theorem add_slots (pc : Fin 142) (h : CanonicalRationalAddition.program pc≠.halt) :
    program (addLabel pc)=ReferenceProgramLabels.instruction addLabel (CanonicalRationalAddition.program pc) := by
  by_cases hp : pc.val=141
  · have he : pc=141 := Fin.ext hp
    subst pc;simp [CanonicalRationalAddition.program] at h
  · simp [program,addLabel,show ¬pc.val+111=110 by omega,show ¬pc.val+111=252 by omega,
      show ¬pc.val+111<111 by omega,show pc.val+111<253 by omega]

theorem run_append {s u v : NaturalState 270} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem outgoing_return {word sw : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (context : OutgoingCostProgram.Context heap b rows sw)
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 270) (stack : List (Frame ℕ 270)) (source : Bits) :
    ∃ ext root,ext.length=OutgoingCostProgram.cells sw word ∧
      NaturalRun program (OutgoingCostProgram.instructions sw word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 109) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (OutgoingCostProgram.result rows sw word) := by
  obtain ⟨ext,root,len,core,rep⟩ := OutgoingCostProgram.outgoing_high
    (OutgoingCostProgram.state heap next a b c d [] source 109) rfl hn rfl input context hi
  have lift := ReferenceProgramLabels.run outLabel OutgoingCostProgram.program program out_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (OutgoingCostProgram.instructions sw word+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 109) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 110) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      OutgoingCostProgram.state,outLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 110)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem addition_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 270)
    (stack : List (Frame ℕ 270)) (source : Bits) :
    ∃ ext root, ext.length=CanonicalRationalAddition.cells x y ∧
      NaturalRun program (CanonicalRationalAddition.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 251) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.add x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalAddition.add_high x y
    (CanonicalRationalAddition.state heap next a b c d [] source 140) rfl hn left right rfl
  have lift := ReferenceProgramLabels.run addLabel CanonicalRationalAddition.program program add_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalAddition.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 251) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 252) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalAddition.state,addLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 252)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

theorem extend_return {heap : NaturalHeap} {a b c : ℕ} {e : Bits×Bits} {q : Walk}
    {rows : List Fraction} {sw : Bits} (edge : Edge heap a e) (walk : StoredWalk heap b q)
    (context : OutgoingCostProgram.Context heap c rows sw) (hi : value e.1<rows.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 270) (stack : List (Frame ℕ 270)) (source : Bits) :
    ∃ ext root,ext.length=cells rows sw e q ∧ NaturalRun program (steps rows sw e q)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 253) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root (result rows sw e q) := by
  obtain ⟨u,v,he,hu,hv⟩ := edge
  obtain ⟨es,score,hq,hes,hscore⟩ := walk
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a b]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
  have scratch0 : h0[next]?=some (.pair a b) := by simp [h0,e0,hn]
  have edge0 : h0[a]?=some (.pair u v) := lookup_extend he e0
  obtain ⟨ew,rw,lw,runW,repW⟩ := outgoing_return (boolList_extend hu e0)
    (PathCostMaterialization.context_extend context e0) hi n0 next next dense0
    ⟨u,c,next,next⟩ 258 frames source
  let h1 := h0++ew
  let n1 := n0+ew.length
  have dense1 : n1=h1.length := by simp [n1,h1,dense0]
  have scratch1 : h1[next]?=some (.pair a b) := lookup_extend scratch0 ew
  have walk1 : h1[b]?=some (.pair es score) := lookup_extend (lookup_extend hq e0) ew
  obtain ⟨ea,ra,la,runA,repA⟩ := addition_return (OutgoingCostProgram.result rows sw e.1) q.cost
    repW (stored_extend (stored_extend hscore e0) ew) n1 next rw dense1
    ⟨rw,score,next,rw⟩ 262 frames source
  let h2 := h1++ea
  let n2 := n1+ea.length
  have dense2 : n2=h2.length := by simp [n2,h2,dense1]
  have scratch2 : h2[next]?=some (.pair a b) := lookup_extend scratch1 ea
  have walk2 : h2[b]?=some (.pair es score) := lookup_extend walk1 ea
  let h3 := h2++[.pair a es]
  let h4 := h3++[.pair n2 ra]
  have t253 : tickNatural program (state heap next a b c d frames source 253)=
      some ⟨state h0 n0 a b c next frames source 254,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,e0,h0,n0]
  have t254 : tickNatural program (state h0 n0 a b c next frames source 254)=
      some ⟨state h0 n0 a c c next frames source 255,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t255 : tickNatural program (state h0 n0 a c c next frames source 255)=
      some ⟨state h0 n0 a c next next frames source 256,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t256 : tickNatural program (state h0 n0 a c next next frames source 256)=
      some ⟨state h0 n0 u c next next frames source 257,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,edge0]
  have t257 : tickNatural program (state h0 n0 u c next next frames source 257)=
      some ⟨state h0 n0 u c next next (⟨258,.r3,⟨u,c,next,next⟩⟩::frames) source 109,[],0⟩ := by
    simp [tickNatural,program,state]
  have t258 : tickNatural program (state h1 n1 u c next rw frames source 258)=
      some ⟨state h1 n1 u b next rw frames source 259,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch1]
  have t259 : tickNatural program (state h1 n1 u b next rw frames source 259)=
      some ⟨state h1 n1 u score next rw frames source 260,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,walk1]
  have t260 : tickNatural program (state h1 n1 u score next rw frames source 260)=
      some ⟨state h1 n1 rw score next rw frames source 261,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t261 : tickNatural program (state h1 n1 rw score next rw frames source 261)=
      some ⟨state h1 n1 rw score next rw (⟨262,.r3,⟨rw,score,next,rw⟩⟩::frames) source 251,[],0⟩ := by
    simp [tickNatural,program,state]
  have t262 : tickNatural program (state h2 n2 rw score next ra frames source 262)=
      some ⟨state h2 n2 a score next ra frames source 263,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch2]
  have t263 : tickNatural program (state h2 n2 a score next ra frames source 263)=
      some ⟨state h2 n2 a b next ra frames source 264,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch2]
  have t264 : tickNatural program (state h2 n2 a b next ra frames source 264)=
      some ⟨state h2 n2 a es next ra frames source 265,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,walk2]
  have t265 : tickNatural program (state h2 n2 a es next ra frames source 265)=
      some ⟨state h3 (n2+1) a n2 next ra frames source 266,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h3]
  have t266 : tickNatural program (state h3 (n2+1) a n2 next ra frames source 266)=
      some ⟨state h4 (n2+2) a n2 next (n2+1) frames source 267,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h4]
  have t267 : tickNatural program (state h4 (n2+2) a n2 next (n2+1) frames source 267)=
      some ⟨state h4 (n2+2) saved.a saved.b saved.c (n2+1) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  let ext := e0++ew++ea++[.pair a es,.pair n2 ra]
  have shape : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,h0,List.append_assoc]
  have len : ext.length=cells rows sw e q := by simp [ext,e0,cells,lw,la];omega
  have count : next+ext.length=n2+2 := by simp [ext,e0,n2,n1,n0];omega
  refine ⟨ext,n2+1,len,?_,?_⟩
  · have first := NaturalRun.step t253 (.step t254 (.step t255 (.step t256 (.step t257 runW))))
    have middle := NaturalRun.step t258 (.step t259 (.step t260 (.step t261 runA)))
    have last := NaturalRun.step t262 (.step t263 (.step t264 (.step t265 (.step t266 (.step t267 (.done _))))))
    have joined := run_append first (run_append middle last)
    rw [shape,count]
    convert joined using 1 <;> simp [steps];omega
  · rw [shape]
    refine ⟨n2,ra,?_,?_,?_⟩
    · simp [h4,h3,dense2]
    · refine EdgeList.cons (head:=a) (tail:=es) ?_ ?_ ?_
      · have hp : h3[n2]?=some (.pair a es) := by simp [h3,dense2]
        exact lookup_extend hp [.pair n2 ra]
      · exact edge_extend (edge_extend (edge_extend (edge_extend
          (edge_extend ⟨u,v,he,hu,hv⟩ e0) ew) ea) [.pair a es]) [.pair n2 ra]
      · exact edgeList_extend (edgeList_extend (edgeList_extend (edgeList_extend
          (edgeList_extend hes e0) ew) ea) [.pair a es]) [.pair n2 ra]
    · exact stored_extend (stored_extend repA [.pair a es]) [.pair n2 ra]

theorem extend_high {heap : NaturalHeap} {a b c : ℕ} {e : Bits×Bits} {q : Walk}
    {rows : List Fraction} {sw : Bits} (edge : Edge heap a e) (walk : StoredWalk heap b q)
    (context : OutgoingCostProgram.Context heap c rows sw) (hi : value e.1<rows.length)
    (next d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext root,ext.length=cells rows sw e q ∧ NaturalRun program (steps rows sw e q+1)
      (state heap next a b c d [] source 268) []
      (state (heap++ext) (next+ext.length) a b c root [] source 269) ∧
      StoredWalk (heap++ext) root (result rows sw e q) := by
  obtain ⟨ext,root,len,core,rep⟩ := extend_return edge walk context hi next d hn ⟨a,b,c,d⟩ 269 [] source
  have call : tickNatural program (state heap next a b c d [] source 268)=
      some ⟨state heap next a b c d [⟨269,.r3,⟨a,b,c,d⟩⟩] source 253,[],0⟩ := by
    simp [tickNatural,program,state]
  exact ⟨ext,root,len,.step call core,rep⟩

end DirectedFlowCutGap.GraphWalkExtension
