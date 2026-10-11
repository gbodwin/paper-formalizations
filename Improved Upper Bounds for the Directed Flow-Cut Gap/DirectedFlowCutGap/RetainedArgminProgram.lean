import DirectedFlowCutGap.RationalComparisonProgram

/-! Actual stable minimum selection over retained costed records. A record
contains a rational-cost pointer and an opaque payload pointer. The selector
returns an original record pointer, preserving that payload and ties; it does
not reconstruct a score-only surrogate. -/
namespace DirectedFlowCutGap.RetainedArgminProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

structure Item where
  score : BinaryRational.Fraction
  payload : ℕ
  address : ℕ

def StoredItem (heap : NaturalHeap) (root : ℕ) (x : Item) : Prop :=
  root=x.address ∧ ∃ cost,heap[root]?=some (.pair cost x.payload) ∧ RationalComparisonProgram.Stored heap cost x.score

inductive ItemList (heap : NaturalHeap) : ℕ → List Item → Prop
  | nil {root : ℕ} : heap[root]?=some .nil → ItemList heap root []
  | cons {root item tail : ℕ} {x : Item} {xs : List Item} :
      heap[root]?=some (.pair item tail) → StoredItem heap item x → ItemList heap tail xs →
      ItemList heap root (x::xs)

theorem stored_extend {heap : NaturalHeap} {root : ℕ} {x : Item}
    (h : StoredItem heap root x) (ext : NaturalHeap) : StoredItem (heap++ext) root x := by
  obtain ⟨hr,cost,hc,hs⟩ := h
  exact ⟨hr,cost,lookup_extend hc ext,RationalComparisonProgram.stored_extend hs ext⟩

theorem list_extend {heap : NaturalHeap} {root : ℕ} {xs : List Item}
    (h : ItemList heap root xs) (ext : NaturalHeap) : ItemList (heap++ext) root xs := by
  induction h with
  | nil h => exact .nil (lookup_extend h ext)
  | cons h hs _ ih => exact .cons (lookup_extend h ext) (stored_extend hs ext) ih

def keep (x y : Item) : Bool := (BinaryRational.le x.score y.score).1
def choose (x y : Item) : Item := if keep x y then x else y

def selectFrom : Item → List Item → Item
  | x,[] => x
  | x,y::ys => selectFrom (choose x y) ys

def scanSteps : Item → List Item → ℕ
  | _,[] => 2
  | x,y::ys => RationalComparisonProgram.instructions x.score y.score+11+
      (if keep x y then 0 else 1)+scanSteps (choose x y) ys

def scanCells : Item → List Item → ℕ
  | _,[] => 0
  | x,y::ys => RationalComparisonProgram.cells x.score y.score+scanCells (choose x y) ys

def label (pc : Fin 158) : Fin 194 := ⟨pc.val,by omega⟩
def program : Program 194 := fun pc =>
  if pc.val=157 then .ret .r3
  else if h : pc.val<158 then
    ReferenceProgramLabels.instruction label (RationalComparisonProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 160 => .branch .r1 176 175 175 161
  | 161 => .field .r2 .r1 true 162
  | 162 => .field .r1 .r1 false 163
  | 163 => .call 190 164 .r3
  | 164 => .branch .r3 175 166 165 175
  | 165 => .move .r1 .r2 160
  | 166 => .move .r0 .r1 165
  | 174 => .make .r3 .nil 175
  | 176 => .move .r3 .r0 177
  | 178 => .branch .r0 174 175 175 179
  | 179 => .field .r1 .r0 true 180
  | 180 => .field .r0 .r0 false 160
  | 190 => .field .r0 .r0 false 191
  | 191 => .field .r1 .r1 false 192
  | 192 => .call 144 193 .r3
  | 193 => .ret .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 194)) (source : Bits) (pc : Fin 194) : NaturalState 194 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem slots (pc : Fin 158) (h : RationalComparisonProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (RationalComparisonProgram.program pc) := by
  by_cases hp : pc.val=157
  · have he : pc=157 := Fin.ext hp
    subst pc;simp [RationalComparisonProgram.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 194} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The old rational-comparison halt becomes a real return to the saved
record-level caller, preserving arbitrary caller frames underneath. -/
theorem rational_return (x y : BinaryRational.Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : RationalComparisonProgram.Stored heap a x) (right : RationalComparisonProgram.Stored heap b y)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 194)
    (stack : List (Frame ℕ 194)) (source : Bits) :
    ∃ ext root,ext.length=RationalComparisonProgram.cells x y ∧
      NaturalRun program (RationalComparisonProgram.instructions x y+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 144) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (BinaryRational.le x y).1) := by
  obtain ⟨u,run,flag,_,_,src,frames,hpc,dense,ext,_⟩ :=
    RationalComparisonProgram.run_high x y (RationalComparisonProgram.state heap next a b c d [] source 144)
      rfl hn left right rfl
  obtain ⟨ext,he,le⟩ := ext
  have lifted := ReferenceProgramLabels.run label RationalComparisonProgram.program program slots run
  have lifted := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lifted
  have body : NaturalRun program (RationalComparisonProgram.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 144) []
      (state (heap++ext) (next+ext.length) u.registers.a u.registers.b u.registers.c u.registers.d
        (⟨pc,.r3,saved⟩::stack) source 157) := by
    have un : u.next=next+ext.length := by rw [dense,he];simp [RationalComparisonProgram.state,hn]
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      RationalComparisonProgram.state,label,state,he,un,src,frames,hpc] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) u.registers.a u.registers.b u.registers.c u.registers.d
        (⟨pc,.r3,saved⟩::stack) source 157)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c u.registers.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,u.registers.d,le,?_,?_⟩
  · simpa using run_append body (.step ret (.done _))
  · simpa only [he,RationalComparisonProgram.state] using flag

/-- A real cost-field adapter preserves the original two records in its saved
frame. Its opaque payload pointers never enter arithmetic. -/
theorem item_compare (x y : Item) {heap : NaturalHeap} {a b : ℕ}
    (left : StoredItem heap a x) (right : StoredItem heap b y)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 194)
    (stack : List (Frame ℕ 194)) (source : Bits) :
    ∃ ext root,ext.length=RationalComparisonProgram.cells x.score y.score ∧
      NaturalRun program (RationalComparisonProgram.instructions x.score y.score+5)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 190) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (keep x y)) := by
  obtain ⟨_,xa,hxa,hx⟩ := left
  obtain ⟨_,yb,hyb,hy⟩ := right
  let frame : Frame ℕ 194 := ⟨pc,.r3,saved⟩
  obtain ⟨ext,root,len,run,flag⟩ := rational_return x.score y.score hx hy next c d hn
    ⟨xa,yb,c,d⟩ 193 (frame::stack) source
  have t190 : tickNatural program (state heap next a b c d (frame::stack) source 190)=
      some ⟨state heap next xa b c d (frame::stack) source 191,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hxa]
  have t191 : tickNatural program (state heap next xa b c d (frame::stack) source 191)=
      some ⟨state heap next xa yb c d (frame::stack) source 192,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hyb]
  have t192 : tickNatural program (state heap next xa yb c d (frame::stack) source 192)=
      some ⟨state heap next xa yb c d (⟨193,.r3,⟨xa,yb,c,d⟩⟩::frame::stack) source 144,[],0⟩ := by
    simp [tickNatural,program,state]
  have t193 : tickNatural program (state (heap++ext) (next+ext.length) xa yb c root (frame::stack) source 193)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,flag⟩
  simpa [Nat.add_assoc] using NaturalRun.step t190 (.step t191 (.step t192
    (run_append run (.step t193 (.done _)))))

/-- A true comparison retains the old record, including equality; false takes
the new record. Both branches resume on the exact saved tail. -/
theorem resume {heap : NaturalHeap} (next a b tail root : ℕ) (flag : Bool)
    (hr : heap[root]?=some (.flag flag)) (source : Bits) :
    NaturalRun program (2+(if flag then 0 else 1))
      (state heap next a b tail root [] source 164) []
      (state heap next (if flag then a else b) tail tail root [] source 160) := by
  cases flag with
  | true =>
    have t164 : tickNatural program (state heap next a b tail root [] source 164)=
        some ⟨state heap next a b tail root [] source 165,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hr,tagBranch]
    have t165 : tickNatural program (state heap next a b tail root [] source 165)=
        some ⟨state heap next a tail tail root [] source 160,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    exact .step t164 (.step t165 (.done _))
  | false =>
    have t164 : tickNatural program (state heap next a b tail root [] source 164)=
        some ⟨state heap next a b tail root [] source 166,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hr,tagBranch]
    have t166 : tickNatural program (state heap next a b tail root [] source 166)=
        some ⟨state heap next b b tail root [] source 165,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t165 : tickNatural program (state heap next b b tail root [] source 165)=
        some ⟨state heap next b tail tail root [] source 160,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    exact .step t164 (.step t166 (.step t165 (.done _)))

/-- The loop keeps an actual original record pointer throughout its stable
fold, and the returned record carries the exact selected opaque payload. -/
theorem scan_high (xs : List Item) (x : Item) {heap : NaturalHeap} {a b : ℕ}
    (best : StoredItem heap a x) (rest : ItemList heap b xs) (next c d : ℕ)
    (hn : next=heap.length) (source : Bits) :
    ∃ ext out,ext.length=scanCells x xs ∧
      NaturalRun program (scanSteps x xs) (state heap next a b c d [] source 160) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧
      StoredItem out.heap out.registers.d (selectFrom x xs) ∧
      out.source=source ∧ out.stack=[] ∧ out.pc=177 ∧ tickNatural program out=none := by
  induction xs generalizing x heap a b next c d with
  | nil =>
    cases rest with
    | nil hb =>
      have t160 : tickNatural program (state heap next a b c d [] source 160)=
          some ⟨state heap next a b c d [] source 176,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hb,tagBranch]
      have t176 : tickNatural program (state heap next a b c d [] source 176)=
          some ⟨state heap next a b c a [] source 177,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact ⟨[],state heap next a b c a [] source 177,rfl,.step t160 (.step t176 (.done _)),
        by simp [state],by simp [state],best,rfl,rfl,rfl,rfl⟩
  | cons y ys ih =>
    cases rest with
    | @cons b item tail y ys hp hy ht =>
      have t160 : tickNatural program (state heap next a b c d [] source 160)=
          some ⟨state heap next a b c d [] source 161,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t161 : tickNatural program (state heap next a b c d [] source 161)=
          some ⟨state heap next a b tail d [] source 162,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t162 : tickNatural program (state heap next a b tail d [] source 162)=
          some ⟨state heap next a item tail d [] source 163,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t163 : tickNatural program (state heap next a item tail d [] source 163)=
          some ⟨state heap next a item tail d [⟨164,.r3,⟨a,item,tail,d⟩⟩] source 190,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,flagRoot,len,cmp,flag⟩ := item_compare x y best hy next tail d hn
        ⟨a,item,tail,d⟩ 164 [] source
      have choice : StoredItem (heap++ext) (if keep x y then a else item) (choose x y) := by
        unfold choose
        split
        · exact stored_extend best ext
        · exact stored_extend hy ext
      obtain ⟨more,out,mlen,scan,he,hnext,selected,src,frames,pc,halt⟩ :=
        ih (choose x y) choice (list_extend ht ext) (next+ext.length) tail flagRoot (by simp [hn])
      have cont := resume (next+ext.length) a item tail flagRoot (keep x y) flag source
      refine ⟨ext++more,out,?_,?_,?_,?_,selected,src,frames,pc,halt⟩
      · simp [scanCells,len,mlen]
      · have all := NaturalRun.step t160 (.step t161 (.step t162 (.step t163
          (run_append cmp (run_append cont scan)))))
        convert all using 1 <;> simp [scanSteps,Nat.add_assoc];omega
      · simpa [List.append_assoc] using he
      · simpa [Nat.add_assoc] using hnext

def select : List Item → Option Item
  | [] => none
  | x::xs => some (selectFrom x xs)
def steps : List Item → ℕ
  | [] => 2
  | x::xs => scanSteps x xs+3
def cells : List Item → ℕ
  | [] => 1
  | x::xs => scanCells x xs

def Selected (heap : NaturalHeap) (root : ℕ) : Option Item → Prop
  | none => heap[root]?=some .nil
  | some x => StoredItem heap root x

/-- Empty inputs return an actual fresh nil. Nonempty inputs return an actual
original record selected by the stable fold, without copying its payload. -/
theorem run_high (xs : List Item) (initial : NaturalState 194)
    (pc0 : initial.pc=178) (hn : initial.next=initial.heap.length)
    (input : ItemList initial.heap initial.registers.a xs) (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (steps xs) initial [] out ∧
      Selected out.heap out.registers.d (select xs) ∧
      ItemList out.heap initial.registers.a xs ∧ out.source=initial.source ∧ out.stack=[] ∧
      out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=cells xs) ∧
      tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn input empty
      subst pc;subst stack
      cases xs with
      | nil =>
        cases input with
        | nil hnil =>
          have t178 : tickNatural program (state heap next a b c d [] source 178)=
              some ⟨state heap next a b c d [] source 174,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
          have t174 : tickNatural program (state heap next a b c d [] source 174)=
              some ⟨state (heap++[.nil]) (next+1) a b c next [] source 175,[],0⟩ := by
            simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
          refine ⟨state (heap++[.nil]) (next+1) a b c next [] source 175,
            .step t178 (.step t174 (.done _)),?_,?_,rfl,rfl,?_,⟨[.nil],rfl,rfl⟩,rfl⟩
          · simp [Selected,select,state,hn]
          · exact list_extend (.nil hnil) _
          · simp [state,hn]
      | cons x xs =>
        cases input with
        | @cons a item tail x xs hp hi ht =>
          have t178 : tickNatural program (state heap next a b c d [] source 178)=
              some ⟨state heap next a b c d [] source 179,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hp,tagBranch]
          have t179 : tickNatural program (state heap next a b c d [] source 179)=
              some ⟨state heap next a tail c d [] source 180,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          have t180 : tickNatural program (state heap next a tail c d [] source 180)=
              some ⟨state heap next item tail c d [] source 160,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          obtain ⟨ext,out,len,run,he,hnext,selected,src,frames,_,halt⟩ := scan_high xs x hi ht next c d hn source
          refine ⟨out,?_,selected,?_,src,frames,?_,⟨ext,he,len⟩,halt⟩
          · simpa [steps,state,Nat.add_assoc] using NaturalRun.step t178 (.step t179 (.step t180 run))
          · rw [he];exact list_extend (.cons hp hi ht) ext
          · rw [hnext,he];simp [hn]

/-- Same-run lower interpretation of the actual stable selector. The original
list and opaque selected record survive; one reached halt is paid. -/
theorem select_bit (xs : List Item) {H B : ℕ} (initial : BitState 194)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=178)
    (hn : value initial.next=initial.heap.length)
    (input : ItemList (eraseState initial).heap (eraseState initial).registers.a xs)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (steps xs) charge initial [] out ∧
      Selected (eraseState out).heap (eraseState out).registers.d (select xs) ∧
      ItemList (eraseState out).heap (eraseState initial).registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells xs) ∧
      out.Bounded (H+steps xs) (B+steps xs) ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 194 H B (steps xs) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,selected,retained,source,stack,_,ext,halt⟩ := run_high xs (eraseState initial) pc0 hn' input empty'
  obtain ⟨charge,out,run,erase,bound,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,src.trans source,?_,?_,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase];exact selected
  · rw [erase];exact retained
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · rw [erase];exact ext

/-- The size parameter bounds the two stored fields separately, including all padding. -/
def Fits (M : ℕ) (x : Item) : Prop := x.score.num.length ≤ M ∧ x.score.den.length ≤ M

theorem choose_fits {M : ℕ} {x y : Item} (hx : Fits M x) (hy : Fits M y) :
    Fits M (choose x y) := by unfold choose;split <;> assumption

theorem compare_steps_bound {M : ℕ} {x y : Item} (hx : Fits M x) (hy : Fits M y) :
    RationalComparisonProgram.instructions x.score y.score ≤ 6400*(M+1)^2 := by
  have h := RationalComparisonProgram.instructions_bound x.score y.score
  have size : RationalComparisonProgram.inputSize x.score y.score ≤ 4*(M+1) := by
    rcases hx with ⟨hx,hxd⟩;rcases hy with ⟨hy,hyd⟩
    dsimp [RationalComparisonProgram.inputSize];omega
  have sq := Nat.mul_self_le_mul_self size
  nlinarith

theorem scan_steps_bound {M : ℕ} (xs : List Item) (x : Item)
    (hx : Fits M x) (hxs : ∀ y∈xs,Fits M y) :
    scanSteps x xs ≤ (6400*(M+1)^2+12)*xs.length+2 := by
  induction xs generalizing x with
  | nil => simp [scanSteps]
  | cons y ys ih =>
    have hy := hxs y (by simp)
    have tail := ih (choose x y) (choose_fits hx hy) (by intro z hz;exact hxs z (by simp [hz]))
    have cmp := compare_steps_bound hx hy
    have branch : (if keep x y then 0 else 1) ≤ 1 := by split <;> omega
    simp only [scanSteps,List.length_cons]
    nlinarith

theorem steps_bound {M : ℕ} (xs : List Item) (hxs : ∀ y∈xs,Fits M y) :
    steps xs ≤ (6400*(M+1)^2+12)*xs.length+5 := by
  cases xs with
  | nil => simp [steps]
  | cons x xs =>
    have h := scan_steps_bound xs x (hxs x (by simp)) (by intro z hz;exact hxs z (by simp [hz]))
    simp only [steps,List.length_cons]
    nlinarith

theorem complete_bound_mono (H B : ℕ) {t u : ℕ} (h : t ≤ u) :
    completeBound 194 H B t ≤ completeBound 194 H B u := by
  unfold completeBound runBound stepBound
  gcongr

/-- The stable selector returns a member, including its original opaque payload. -/
theorem selectFrom_mem (xs : List Item) (x : Item) : selectFrom x xs∈x::xs := by
  induction xs generalizing x with
  | nil => simp [selectFrom]
  | cons y ys ih =>
    change selectFrom (choose x y) ys∈x::y::ys
    rcases List.mem_cons.mp (ih (choose x y)) with he | hm
    · rw [he]
      unfold choose
      split <;> simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

end DirectedFlowCutGap.RetainedArgminProgram
