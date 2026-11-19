import DirectedFlowCutGap.CandidatePortAdjacencyProgram
import DirectedFlowCutGap.WordPairProductProgram

/-! Construct the stored candidate network descriptors in canonical order. -/

namespace DirectedFlowCutGap.CandidateNodeListsProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList list_extend)
open CandidateEnumeration
open CandidatePortAdjacencyProgram (Kind kind tag vertex)

def taggedPort {n : ℕ} (k : Kind) (v : Fin n) : Port n :=
  match k with
  | .core => .inl v
  | .start => .inr (.inl v)
  | .finish => .inr (.inr v)

@[simp] theorem tagged_kind {n : ℕ} (k : Kind) (v : Fin n) : kind (taggedPort k v)=k := by
  cases k <;> rfl

@[simp] theorem tagged_vertex {n : ℕ} (k : Kind) (v : Fin n) : vertex (taggedPort k v)=v := by
  cases k <;> rfl

def PortAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (p : Port n) : Prop :=
  ∃ tagRoot address,heap[root]?=some (.pair tagRoot address) ∧
    heap[tagRoot]?=some (tag (kind p)) ∧ BoolList heap address (vertex p).val.bits

theorem port_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {p : Port n} (stored : PortAt heap root p)
    (ext : NaturalHeap) : PortAt (heap++ext) root p := by
  obtain ⟨tagRoot,address,pair,mode,idx⟩ := stored
  exact ⟨tagRoot,address,lookup_extend pair ext,lookup_extend mode ext,boolList_extend idx ext⟩

def Descriptor {n L : ℕ} (heap : NaturalHeap) (root : ℕ) : Network n L→Prop
  | .inr terminal => heap[root]?=some (.flag terminal)
  | .inl ((p,side),l) =>
    ∃ port fields sign level,heap[root]?=some (.pair port fields) ∧ PortAt heap port p ∧
      heap[fields]?=some (.pair sign level) ∧ heap[sign]?=some (.flag side) ∧
      BoolList heap level l.val.bits

theorem descriptor_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {a : Network n L}
    (stored : Descriptor heap root a) (ext : NaturalHeap) : Descriptor (heap++ext) root a := by
  rcases a with ⟨⟨p,side⟩,level⟩ | terminal
  · obtain ⟨port,fields,sign,label,hp,rep,hf,hs,hl⟩ := stored
    exact ⟨port,fields,sign,label,lookup_extend hp ext,port_extend rep ext,lookup_extend hf ext,
      lookup_extend hs ext,boolList_extend hl ext⟩
  · exact lookup_extend stored ext

inductive Stored {n L : ℕ} (heap : NaturalHeap) : ℕ→List (Network n L)→Prop
  | nil {root} : heap[root]?=some .nil → Stored heap root []
  | cons {root head tail a as} : heap[root]?=some (.pair head tail) →
      Descriptor heap head a → Stored heap tail as → Stored heap root (a::as)

theorem stored_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {as : List (Network n L)}
    (stored : Stored heap root as) (ext : NaturalHeap) : Stored (heap++ext) root as := by
  induction stored with
  | nil read => exact .nil (lookup_extend read ext)
  | cons read descriptor _ ih => exact .cons (lookup_extend read ext) (descriptor_extend descriptor ext) ih

def levelBlock {n L : ℕ} (p : Port n) (side : Bool) (ls : List (Fin (L+1))) : List (Network n L) :=
  ls.map fun l => .inl ((p,side),l)

def portBlock {n L : ℕ} (k : Kind) (vs : List (Fin n)) (ls : List (Fin (L+1))) : List (Network n L) :=
  vs.flatMap fun v => levelBlock (taggedPort k v) false ls ++ levelBlock (taggedPort k v) true ls

theorem blocks_eq_order (n L : ℕ) :
    portBlock .core (List.finRange n) (List.finRange (L+1))++
      portBlock .start (List.finRange n) (List.finRange (L+1))++
      portBlock .finish (List.finRange n) (List.finRange (L+1))++
      [.inr false,.inr true] = networkOrder n L := by
  simp [networkOrder,portBlock,levelBlock,taggedPort,List.flatMap_append,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,List.append_assoc,Function.comp_def]

def program : Program 48 := fun pc => match pc.val with
  | 0 => .make .r3 .nil 1
  | 1 => .make .r2 (.flag true) 2
  | 2 => .make .r3 (.pair .r2 .r3) 3
  | 3 => .make .r2 (.flag false) 4
  | 4 => .make .r3 (.pair .r2 .r3) 5
  | 5 => .make .r2 (.flag true) 6
  | 6 => .call 16 7 .r3
  | 7 => .make .r2 (.flag false) 8
  | 8 => .call 16 9 .r3
  | 9 => .make .r2 .nil 10
  | 10 => .call 16 11 .r3
  | 16 => .branch .r0 17 47 47 18
  | 17 => .ret .r3
  | 18 => .call 24 19 .r3
  | 19 => .field .r0 .r0 false 20
  | 20 => .make .r0 (.pair .r2 .r0) 21
  | 21 => .make .r2 (.flag true) 22
  | 22 => .call 32 23 .r3
  | 23 => .make .r2 (.flag false) 26
  | 24 => .field .r0 .r0 true 16
  | 26 => .call 32 27 .r3
  | 27 => .ret .r3
  | 32 => .branch .r1 17 47 47 33
  | 33 => .call 38 34 .r3
  | 34 => .field .r1 .r1 false 35
  | 35 => .make .r1 (.pair .r2 .r1) 36
  | 36 => .make .r1 (.pair .r0 .r1) 37
  | 37 => .make .r3 (.pair .r1 .r3) 17
  | 38 => .field .r1 .r1 true 32
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 48))
    (tape : Bits) (pc : Fin 48) : NaturalState 48 := ⟨heap,heap.length,r,stack,pc,tape⟩

def levelSteps (levels : ℕ) : ℕ := 8*levels+2
def portSteps (vertices levels : ℕ) : ℕ := vertices*(16*levels+14)+2
def steps (vertices levels : ℕ) : ℕ := 3*portSteps vertices levels+11

private theorem appended_at (heap ext : NaturalHeap) (i : ℕ) :
    (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

set_option maxHeartbeats 1000000 in
private theorem level_return {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {p : Port n} {side : Bool} {ls : List (Fin (L+1))} {suffix : List (Network n L)}
    (port : PortAt heap r.a p) (levels : WordList heap r.b (ls.map fun l => l.val.bits))
    (sign : heap[r.c]?=some (.flag side)) (acc : Stored heap r.d suffix)
    (caller : Frame ℕ 48) (stack : List (Frame ℕ 48)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (levelBlock p side ls++suffix) ∧
      NaturalRun program (levelSteps ls.length) (state heap r (caller::stack) tape 32) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction ls generalizing heap r caller stack with
  | nil =>
    cases levels with
    | nil read =>
      refine ⟨[],r.d,by simpa [levelBlock] using acc,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,levelSteps,tickNatural,Registers.get,read,tagBranch]
  | cons l ls ih =>
    simp only [List.map_cons] at levels
    cases levels with
    | @cons _ head tail _ _ pair lp rest =>
      let saved := caller::stack
      let inner : Frame ℕ 48 := ⟨34,.r3,r⟩
      let args := r.set .r1 tail
      have prep : NaturalRun program 3 (state heap r saved tape 32) []
          (state heap args (inner::saved) tape 32) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,pair,args,inner]
      obtain ⟨ext,tailRoot,rep,body⟩ := ih (r:=args) port rest sign acc inner saved
      let mid := heap++ext
      let i := mid.length
      let cells : NaturalHeap := [.pair r.c head,.pair r.a i,.pair (i+1) tailRoot]
      have read : mid[r.b]?=some (.pair head tail) := lookup_extend pair ext
      have finish : NaturalRun program 5 (state mid (r.set .r3 tailRoot) saved tape 34) []
          (state (mid++cells) (caller.saved.set caller.destination (i+2)) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,read,saved,
          i,cells,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
      have hp : (mid++cells)[i+1]?=some (.pair r.a i) := appended_at mid cells 1
      have hf : (mid++cells)[i]?=some (.pair r.c head) := by simp [i,cells]
      have hb : (mid++cells)[i+2]?=some (.pair (i+1) tailRoot) := appended_at mid cells 2
      have desc : Descriptor (mid++cells) (i+1) (.inl ((p,side),l)) :=
        ⟨r.a,i,r.c,head,hp,port_extend (port_extend port ext) cells,hf,lookup_extend (lookup_extend sign ext) cells,
          boolList_extend (boolList_extend lp ext) cells⟩
      have stored : Stored (mid++cells) (i+2) (levelBlock p side (l::ls)++suffix) :=
        .cons hb desc (stored_extend rep cells)
      refine ⟨ext++cells,i+2,?_,?_⟩
      · simpa only [mid,List.append_assoc] using stored
      · have full := append_run prep (append_run body finish)
        have count : 3+(levelSteps ls.length+5)=levelSteps (l::ls).length := by simp [levelSteps,Nat.mul_add]; omega
        rw [← count]
        simpa only [mid,List.append_assoc,List.nil_append] using full

set_option maxHeartbeats 1500000 in
private theorem port_return {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {k : Kind} {vs : List (Fin n)} {ls : List (Fin (L+1))} {suffix : List (Network n L)}
    (vertices : WordList heap r.a (vs.map fun v => v.val.bits)) (levels : WordList heap r.b (ls.map fun l => l.val.bits))
    (mode : heap[r.c]?=some (tag k)) (acc : Stored heap r.d suffix)
    (caller : Frame ℕ 48) (stack : List (Frame ℕ 48)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (portBlock k vs ls++suffix) ∧
      NaturalRun program (portSteps vs.length ls.length) (state heap r (caller::stack) tape 16) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction vs generalizing heap r caller stack with
  | nil =>
    cases vertices with
    | nil read =>
      refine ⟨[],r.d,by simpa [portBlock] using acc,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,portSteps,tickNatural,Registers.get,read,tagBranch]
  | cons v vs ih =>
    simp only [List.map_cons] at vertices
    cases vertices with
    | @cons _ head tail _ _ pair vp rest =>
      let saved := caller::stack
      let inner : Frame ℕ 48 := ⟨19,.r3,r⟩
      let args := r.set .r0 tail
      have prep : NaturalRun program 3 (state heap r saved tape 16) []
          (state heap args (inner::saved) tape 16) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,pair,args,inner]
      obtain ⟨ep,tailRoot,tailRep,body⟩ := ih (r:=args) rest levels mode acc inner saved
      let mid := heap++ep
      let i := mid.length
      let cells : NaturalHeap := [.pair r.c head,.flag true]
      let tagged := mid++cells
      let ready := ((r.set .r3 tailRoot).set .r0 i).set .r2 (i+1)
      let afterFrame : Frame ℕ 48 := ⟨23,.r3,ready⟩
      have read : mid[r.a]?=some (.pair head tail) := lookup_extend pair ep
      have prepare : NaturalRun program 4 (state mid (r.set .r3 tailRoot) saved tape 19) []
          (state tagged ready (afterFrame::saved) tape 32) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,read,ready,
          i,cells,tagged,afterFrame,allocateNatural,Recipe.cell,List.append_assoc]
      have port : PortAt tagged ready.a (taggedPort k v) :=
        ⟨r.c,head,by simp [tagged,ready,i,cells,Registers.set],by
          simpa only [tagged_kind] using lookup_extend (lookup_extend mode ep) cells,by
          simpa only [tagged_vertex] using boolList_extend (boolList_extend vp ep) cells⟩
      have sign : tagged[ready.c]?=some (.flag true) := appended_at mid cells 1
      have levelRep : WordList tagged ready.b (ls.map fun l => l.val.bits) := list_extend (list_extend levels ep) cells
      obtain ⟨et,after,afterNodes,afterRun⟩ := level_return (r:=ready) port levelRep sign
        (stored_extend tailRep cells) afterFrame saved tape
      let grown := tagged++et
      let before := ((ready.set .r3 after).set .r2 grown.length)
      let beforeFrame : Frame ℕ 48 := ⟨27,.r3,before⟩
      have switch : NaturalRun program 2 (state grown (ready.set .r3 after) saved tape 23) []
          (state (grown++[.flag false]) before (beforeFrame::saved) tape 32) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
          Recipe.cell,before,beforeFrame]
      have newSign : (grown++[.flag false])[before.c]?=some (.flag false) := by simp [before,Registers.set]
      obtain ⟨ef,root,beforeNodes,beforeRun⟩ := level_return (r:=before) (port_extend (port_extend port et) [.flag false])
        (list_extend (list_extend levelRep et) [.flag false]) newSign (stored_extend afterNodes [.flag false]) beforeFrame saved tape
      have ret : tickNatural program (state ((grown++[.flag false])++ef) (before.set .r3 root) saved tape 27)=
          some ⟨state ((grown++[.flag false])++ef) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,Registers.set,saved]
      refine ⟨ep++cells++et++[.flag false]++ef,root,?_,?_⟩
      · simpa only [mid,tagged,grown,portBlock,List.flatMap_cons,List.append_assoc] using beforeNodes
      · have full := append_run prep (append_run body (append_run prepare
          (append_run afterRun (append_run switch (append_run beforeRun (.step ret (.done _)))))))
        have num : 3+(portSteps vs.length ls.length+(4+(levelSteps ls.length+(2+(levelSteps ls.length+1))))) =
            portSteps (v::vs).length ls.length := by simp [portSteps,levelSteps,Nat.succ_mul]; omega
        rw [← num]
        simpa only [mid,tagged,grown,List.append_assoc,List.nil_append,Nat.zero_add] using full

set_option maxHeartbeats 1000000 in
private theorem terminals {n L : ℕ} (heap : NaturalHeap) (r : Registers ℕ) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ),
      Stored (heap++ext) args.d ([.inr false,.inr true] : List (Network n L)) ∧
      (heap++ext)[args.c]?=some (tag .finish) ∧ args.a=r.a ∧ args.b=r.b ∧
      NaturalRun program 6 (state heap r [] tape 0) [] (state (heap++ext) args [] tape 6) := by
  let i := heap.length
  let ext : NaturalHeap := [.nil,.flag true,.pair (i+1) i,.flag false,.pair (i+3) (i+2),.flag true]
  let args := (r.set .r3 (i+4)).set .r2 (i+5)
  refine ⟨ext,args,.cons (appended_at heap ext 4) (appended_at heap ext 3)
    (.cons (appended_at heap ext 2) (appended_at heap ext 1) (.nil (appended_at heap ext 0))),
    appended_at heap ext 5,rfl,rfl,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
    Recipe.cell,i,ext,args,List.append_assoc,Nat.add_assoc]

theorem natural_nodes {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (vertices : WordList heap r.a ((List.finRange n).map fun v => v.val.bits))
    (levels : WordList heap r.b ((List.finRange (L+1)).map fun l => l.val.bits)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Stored (heap++ext) root (networkOrder n L) ∧
      NaturalRun program (steps n (L+1)) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 11) := by
  obtain ⟨e0,r0,base,finishTag,va,lb,init⟩ := terminals (n:=n) (L:=L) heap r tape
  let h0 := heap++e0
  let f0 : Frame ℕ 48 := ⟨7,.r3,r0⟩
  have enter : tickNatural program (state h0 r0 [] tape 6)=some ⟨state h0 r0 [f0] tape 16,[],0⟩ := rfl
  have v0 : WordList h0 r0.a ((List.finRange n).map fun v => v.val.bits) := va.symm ▸ list_extend vertices e0
  have l0 : WordList h0 r0.b ((List.finRange (L+1)).map fun l => l.val.bits) := lb.symm ▸ list_extend levels e0
  obtain ⟨ef,f,rfinish,runFinish⟩ := port_return v0 l0 finishTag base f0 [] tape
  let hf := h0++ef
  let prepStart := r0.set .r3 f
  let r1 := prepStart.set .r2 hf.length
  let f1 : Frame ℕ 48 := ⟨9,.r3,r1⟩
  have tagStart : NaturalRun program 2 (state hf prepStart [] tape 7) []
      (state (hf++[.flag false]) r1 [f1] tape 16) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell,prepStart,r1,f1]
  have startTag : (hf++[.flag false])[r1.c]?=some (tag .start) := by simp [r1,prepStart,tag,Registers.set]
  have v1 : WordList (hf++[.flag false]) r1.a ((List.finRange n).map fun v => v.val.bits) :=
    list_extend (list_extend v0 ef) [.flag false]
  have l1 : WordList (hf++[.flag false]) r1.b ((List.finRange (L+1)).map fun l => l.val.bits) :=
    list_extend (list_extend l0 ef) [.flag false]
  obtain ⟨es,s,rstart,runStart⟩ := port_return v1 l1 startTag (stored_extend rfinish [.flag false]) f1 [] tape
  let hs := hf++[.flag false]++es
  let prepCore := r1.set .r3 s
  let r2 := prepCore.set .r2 hs.length
  let f2 : Frame ℕ 48 := ⟨11,.r3,r2⟩
  have tagCore : NaturalRun program 2 (state hs prepCore [] tape 9) []
      (state (hs++[.nil]) r2 [f2] tape 16) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell,prepCore,r2,f2]
  have coreTag : (hs++[.nil])[r2.c]?=some (tag .core) := by simp [r2,prepCore,tag,Registers.set]
  obtain ⟨ec,root,rep,runCore⟩ := port_return (r:=r2) (list_extend (list_extend v1 es) [.nil])
    (list_extend (list_extend l1 es) [.nil]) coreTag (stored_extend rstart [.nil]) f2 [] tape
  refine ⟨e0++ef++[.flag false]++es++[.nil]++ec,r2,root,?_,?_⟩
  · rw [← blocks_eq_order]
    simpa only [hs,hf,h0,List.append_assoc] using rep
  · have full := append_run init (.step enter (append_run runFinish (append_run tagStart
      (append_run runStart (append_run tagCore runCore)))))
    simp only [List.length_finRange] at full
    have count : 6+(portSteps n (L+1)+(2+(portSteps n (L+1)+(2+portSteps n (L+1)))))+1 = steps n (L+1) := by
      unfold steps
      omega
    rw [← count]
    simpa only [h0,hf,hs,f0,f1,f2,prepStart,prepCore,List.append_assoc,List.nil_append,Nat.add_assoc,
      Nat.add_comm 1] using full

end DirectedFlowCutGap.CandidateNodeListsProgram
