import DirectedFlowCutGap.MaterializedPathSum
import DirectedFlowCutGap.RetainedArgminProgram

/-! A real outer traversal computes every candidate cost from retained path
indices and constructs the exact record list consumed by stable selection.
Every original opaque payload is retained across cost computation. Duplicate occurrences
are retained separately; their newly allocated addresses are occurrence-based. -/
namespace DirectedFlowCutGap.CostedCandidateMaterialization
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

structure Candidate where
  words : List Bits
  sourceWord : Bits
  payload : ℕ

def StoredCandidate (heap : NaturalHeap) (p : ℕ) (x : Candidate) : Prop :=
  ∃ path metadata sw,heap[p]?=some (.pair path metadata) ∧ heap[metadata]?=some (.pair sw x.payload) ∧
    PathCostMaterialization.WordList heap path x.words ∧ BoolList heap sw x.sourceWord

inductive CandidateList (heap : NaturalHeap) : ℕ → List Candidate → Prop
  | nil {p} : heap[p]?=some .nil → CandidateList heap p []
  | cons {p head tail x xs} : heap[p]?=some (.pair head tail) →
      StoredCandidate heap head x → CandidateList heap tail xs → CandidateList heap p (x::xs)

theorem stored_extend {heap : NaturalHeap} {p : ℕ} {x : Candidate}
    (h : StoredCandidate heap p x) (ext : NaturalHeap) : StoredCandidate (heap++ext) p x := by
  obtain ⟨path,metadata,sw,hr,hm,hw,hs⟩ := h
  exact ⟨path,metadata,sw,lookup_extend hr ext,lookup_extend hm ext,
    PathCostMaterialization.list_extend hw ext,boolList_extend hs ext⟩

theorem list_extend {heap : NaturalHeap} {p : ℕ} {xs : List Candidate}
    (h : CandidateList heap p xs) (ext : NaturalHeap) : CandidateList (heap++ext) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hx _ ih => exact .cons (lookup_extend hp ext) (stored_extend hx ext) ih

def score (rows : List Fraction) (x : Candidate) : Fraction :=
  MaterializedPathSum.result rows x.sourceWord x.words

def steps (rows : List Fraction) : List Candidate → ℕ
  | [] => 3
  | x::xs => steps rows xs+MaterializedPathSum.steps rows x.sourceWord x.words+21

def cells (rows : List Fraction) : List Candidate → ℕ
  | [] => 1
  | x::xs => cells rows xs+MaterializedPathSum.cells rows x.sourceWord x.words+4

/-- Allocation addresses are computed separately for every occurrence. -/
def items (rows : List Fraction) (next : ℕ) : List Candidate → List RetainedArgminProgram.Item
  | [] => []
  | x::xs => ⟨score rows x,x.payload,
      next+cells rows xs+2+MaterializedPathSum.cells rows x.sourceWord x.words⟩::items rows next xs

def label (pc : Fin 284) : Fin 307 := ⟨pc.val,by omega⟩
def program : Program 307 := fun pc =>
  if pc.val=283 then .ret .r3
  else if h : pc.val<284 then
    ReferenceProgramLabels.instruction label (MaterializedPathSum.program ⟨pc.val,h⟩)
  else match pc.val with
  | 284 => .branch .r0 285 306 306 287
  | 285 => .make .r3 .nil 286
  | 286 => .ret .r3
  | 287 => .field .r2 .r0 false 288
  | 288 => .field .r0 .r0 true 289
  | 289 => .call 284 290 .r3
  | 290 => .make .r2 (.pair .r2 .r3) 291
  | 291 => .field .r0 .r2 false 292
  | 292 => .field .r0 .r0 true 293
  | 293 => .field .r0 .r0 false 294
  | 294 => .make .r1 (.pair .r1 .r0) 295
  | 295 => .field .r0 .r2 false 296
  | 296 => .field .r0 .r0 false 297
  | 297 => .call 282 298 .r3
  | 298 => .field .r0 .r2 false 299
  | 299 => .field .r0 .r0 true 300
  | 300 => .field .r0 .r0 true 301
  | 301 => .make .r3 (.pair .r3 .r0) 302
  | 302 => .field .r2 .r2 true 303
  | 303 => .make .r3 (.pair .r3 .r2) 304
  | 304 => .ret .r3
  | 305 => .call 284 306 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 307)) (source : Bits) (pc : Fin 307) : NaturalState 307 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem slots (pc : Fin 284) (h : MaterializedPathSum.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (MaterializedPathSum.program pc) := by
  by_cases hp : pc.val=283
  · have he : pc=283 := Fin.ext hp
    subst pc;simp [MaterializedPathSum.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 307} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem path_return {words : List Bits} {sw : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : PathCostMaterialization.WordList heap a words)
    (context : OutgoingCostProgram.Context heap b rows sw) (valid : ∀ w∈words,value w<rows.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 307)
    (stack : List (Frame ℕ 307)) (source : Bits) :
    ∃ ext root,ext.length=MaterializedPathSum.cells rows sw words ∧
      NaturalRun program (MaterializedPathSum.steps rows sw words+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 282) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (MaterializedPathSum.result rows sw words) := by
  obtain ⟨ext,root,len,core,rep,_⟩ := MaterializedPathSum.sum_high
    (MaterializedPathSum.state heap next a b c d [] source 282) rfl hn rfl input context valid
  have lift := ReferenceProgramLabels.run label MaterializedPathSum.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (MaterializedPathSum.steps rows sw words+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 282) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 283) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      MaterializedPathSum.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 283)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem materialize_return {xs : List Candidate} {rows : List Fraction} {heap : NaturalHeap} {p : ℕ}
    (input : CandidateList heap p xs)
    (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length) (next table c d : ℕ)
    (hn : next=heap.length) (ht : WordPairTableRead.Table heap table (IndexedRationalRead.fields rows))
    (saved : Registers ℕ) (pc : Fin 307) (stack : List (Frame ℕ 307)) (source : Bits) :
    ∃ ext root,ext.length=cells rows xs ∧ NaturalRun program (steps rows xs)
      (state heap next p table c d (⟨pc,.r3,saved⟩::stack) source 284) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RetainedArgminProgram.ItemList (heap++ext) root (items rows next xs) := by
  induction input generalizing next table c d saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t284 : tickNatural program (state heap next p table c d frames source 284)=
        some ⟨state heap next p table c d frames source 285,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t285 : tickNatural program (state heap next p table c d frames source 285)=
        some ⟨state (heap++[.nil]) (next+1) p table c next frames source 286,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
    have t286 : tickNatural program (state (heap++[.nil]) (next+1) p table c next frames source 286)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[.nil],next,rfl,.step t284 (.step t285 (.step t286 (.done _))),.nil (by simp [hn])⟩
  | @cons p head tail x xs hp hx hxs ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have vx := valid x (by simp)
    have vs : ∀ y∈xs,∀ w∈y.words,value w<rows.length := fun y h => valid y (by simp [h])
    obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih vs next table head d hn ht ⟨tail,table,head,d⟩ 290 frames
    obtain ⟨path,metadata,sw,hr,hm,hw,hs⟩ := hx
    let h1 := heap++et
    let n1 := next+et.length
    have dense1 : n1=h1.length := by simp [n1,h1,hn]
    let setup : NaturalHeap := [.pair head rt,.pair table sw]
    let h2 := h1++setup
    let n2 := n1+2
    have dense2 : n2=h2.length := by simp [n2,h2,setup,dense1]
    have pathRep : PathCostMaterialization.WordList h2 path x.words :=
      PathCostMaterialization.list_extend (PathCostMaterialization.list_extend hw et) setup
    have context : OutgoingCostProgram.Context h2 (n1+1) rows x.sourceWord := by
      refine ⟨table,sw,?_,?_,?_⟩
      · simp [h2,setup,dense1]
      · exact BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend ht et) setup
      · exact boolList_extend (boolList_extend hs et) setup
    obtain ⟨ec,rc,lc,costRun,costRep⟩ := path_return pathRep context vx n2 n1 rt dense2
      ⟨path,n1+1,n1,rt⟩ 298 frames source
    let h3 := h2++ec
    let n3 := n2+ec.length
    have dense3 : n3=h3.length := by simp [n3,h3,dense2]
    have rec1 : h1[head]?=some (.pair path metadata) := lookup_extend hr et
    have meta1 : h1[metadata]?=some (.pair sw x.payload) := lookup_extend hm et
    have scratch2 : h2[n1]?=some (.pair head rt) := by simp [h2,setup,dense1]
    have scratch3 : h3[n1]?=some (.pair head rt) := lookup_extend scratch2 ec
    have recScratch := lookup_extend rec1 [.pair head rt]
    have metaScratch := lookup_extend meta1 [.pair head rt]
    have rec2 : h2[head]?=some (.pair path metadata) := lookup_extend rec1 setup
    have rec3 : h3[head]?=some (.pair path metadata) := lookup_extend rec2 ec
    have meta3 : h3[metadata]?=some (.pair sw x.payload) := lookup_extend (lookup_extend meta1 setup) ec
    have scratchFinal := lookup_extend scratch3 [.pair rc x.payload]
    have t284 : tickNatural program (state heap next p table c d frames source 284)=
        some ⟨state heap next p table c d frames source 287,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t287 : tickNatural program (state heap next p table c d frames source 287)=
        some ⟨state heap next p table head d frames source 288,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t288 : tickNatural program (state heap next p table head d frames source 288)=
        some ⟨state heap next tail table head d frames source 289,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t289 : tickNatural program (state heap next tail table head d frames source 289)=
        some ⟨state heap next tail table head d (⟨290,.r3,⟨tail,table,head,d⟩⟩::frames) source 284,[],0⟩ := by
      simp [tickNatural,program,state]
    have t290 : tickNatural program (state h1 n1 tail table head rt frames source 290)=
        some ⟨state (h1++[.pair head rt]) (n1+1) tail table n1 rt frames source 291,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
    have t291 : tickNatural program (state (h1++[.pair head rt]) (n1+1) tail table n1 rt frames source 291)=
        some ⟨state (h1++[.pair head rt]) (n1+1) head table n1 rt frames source 292,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,dense1]
    have t292 : tickNatural program (state (h1++[.pair head rt]) (n1+1) head table n1 rt frames source 292)=
        some ⟨state (h1++[.pair head rt]) (n1+1) metadata table n1 rt frames source 293,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,recScratch]
    have t293 : tickNatural program (state (h1++[.pair head rt]) (n1+1) metadata table n1 rt frames source 293)=
        some ⟨state (h1++[.pair head rt]) (n1+1) sw table n1 rt frames source 294,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,metaScratch]
    have t294 : tickNatural program (state (h1++[.pair head rt]) (n1+1) sw table n1 rt frames source 294)=
        some ⟨state h2 n2 sw (n1+1) n1 rt frames source 295,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,n2,setup,List.append_assoc,Nat.add_assoc]
    have t295 : tickNatural program (state h2 n2 sw (n1+1) n1 rt frames source 295)=
        some ⟨state h2 n2 head (n1+1) n1 rt frames source 296,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch2]
    have t296 : tickNatural program (state h2 n2 head (n1+1) n1 rt frames source 296)=
        some ⟨state h2 n2 path (n1+1) n1 rt frames source 297,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,rec2]
    have t297 : tickNatural program (state h2 n2 path (n1+1) n1 rt frames source 297)=
        some ⟨state h2 n2 path (n1+1) n1 rt (⟨298,.r3,⟨path,n1+1,n1,rt⟩⟩::frames) source 282,[],0⟩ := by
      simp [tickNatural,program,state]
    have t298 : tickNatural program (state h3 n3 path (n1+1) n1 rc frames source 298)=
        some ⟨state h3 n3 head (n1+1) n1 rc frames source 299,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch3]
    have t299 : tickNatural program (state h3 n3 head (n1+1) n1 rc frames source 299)=
        some ⟨state h3 n3 metadata (n1+1) n1 rc frames source 300,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,rec3]
    have t300 : tickNatural program (state h3 n3 metadata (n1+1) n1 rc frames source 300)=
        some ⟨state h3 n3 x.payload (n1+1) n1 rc frames source 301,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,meta3]
    have t301 : tickNatural program (state h3 n3 x.payload (n1+1) n1 rc frames source 301)=
        some ⟨state (h3++[.pair rc x.payload]) (n3+1) x.payload (n1+1) n1 n3 frames source 302,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
    have t302 : tickNatural program (state (h3++[.pair rc x.payload]) (n3+1) x.payload (n1+1) n1 n3 frames source 302)=
        some ⟨state (h3++[.pair rc x.payload]) (n3+1) x.payload (n1+1) rt n3 frames source 303,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratchFinal]
    have t303 : tickNatural program (state (h3++[.pair rc x.payload]) (n3+1) x.payload (n1+1) rt n3 frames source 303)=
        some ⟨state (h3++[.pair rc x.payload,.pair n3 rt]) (n3+2) x.payload (n1+1) rt (n3+1) frames source 304,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,List.append_assoc,Nat.add_assoc]
    have t304 : tickNatural program (state (h3++[.pair rc x.payload,.pair n3 rt]) (n3+2) x.payload (n1+1) rt (n3+1) frames source 304)=
        some ⟨state (h3++[.pair rc x.payload,.pair n3 rt]) (n3+2) saved.a saved.b saved.c (n3+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    have pre : NaturalRun program 4 (state heap next p table c d frames source 284) []
        (state heap next tail table head d (⟨290,.r3,⟨tail,table,head,d⟩⟩::frames) source 284) :=
      .step t284 (.step t287 (.step t288 (.step t289 (.done _))))
    have middle : NaturalRun program 8 (state h1 n1 tail table head rt frames source 290) []
        (state h2 n2 path (n1+1) n1 rt (⟨298,.r3,⟨path,n1+1,n1,rt⟩⟩::frames) source 282) :=
      .step t290 (.step t291 (.step t292 (.step t293 (.step t294 (.step t295 (.step t296 (.step t297 (.done _))))))))
    have post : NaturalRun program 7 (state h3 n3 path (n1+1) n1 rc frames source 298) []
        (state (h3++[.pair rc x.payload,.pair n3 rt]) (n3+2) saved.a saved.b saved.c (n3+1) stack source pc) :=
      .step t298 (.step t299 (.step t300 (.step t301 (.step t302 (.step t303 (.step t304 (.done _)))))))
    refine ⟨et++setup++ec++[.pair rc x.payload,.pair n3 rt],n3+1,?_,?_,?_⟩
    · simp [cells,setup,lt,lc,Nat.add_assoc]
    · have all := run_append pre (run_append tailRun (run_append middle (run_append costRun post)))
      convert all using 1 <;> simp [steps,h3,h2,h1,n3,n2,n1,setup,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> first | omega | (congr 1; omega)
    · have itemRep : RetainedArgminProgram.StoredItem (h3++[.pair rc x.payload,.pair n3 rt]) n3
          ⟨score rows x,x.payload,next+cells rows xs+2+MaterializedPathSum.cells rows x.sourceWord x.words⟩ := by
        refine ⟨?_,rc,?_,RationalComparisonProgram.stored_extend costRep _⟩
        · simp [n3,n2,n1,lt,lc]
        · simp [dense3]
      have resultRep : RetainedArgminProgram.ItemList (h3++[.pair rc x.payload,.pair n3 rt]) (n3+1)
          (items rows next (x::xs)) :=
        .cons (by simp [dense3]) itemRep
          (RetainedArgminProgram.list_extend (RetainedArgminProgram.list_extend
            (RetainedArgminProgram.list_extend tailRep setup) ec) _)
      simpa [h3,h2,h1,List.append_assoc] using resultRep

theorem materialize_high {xs : List Candidate} {rows : List Fraction} (initial : NaturalState 307)
    (pc0 : initial.pc=305) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : CandidateList initial.heap initial.registers.a xs)
    (table : WordPairTableRead.Table initial.heap initial.registers.b (IndexedRationalRead.fields rows))
    (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length) :
    ∃ ext root,ext.length=cells rows xs ∧ NaturalRun program (steps rows xs+1) initial []
      (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
        initial.registers.b initial.registers.c root [] initial.source 306) ∧
      RetainedArgminProgram.ItemList (initial.heap++ext) root (items rows initial.next xs) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input table
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 305)=
          some ⟨state heap next a b c d [⟨306,.r3,⟨a,b,c,d⟩⟩] source 284,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := materialize_return input valid next b c d hn table ⟨a,b,c,d⟩ 306 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_assoc,state] using NaturalRun.step first run,rep⟩

end DirectedFlowCutGap.CostedCandidateMaterialization
