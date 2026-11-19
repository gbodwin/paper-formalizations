import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.PathCostMaterialization
import DirectedFlowCutGap.RetainedGridState

/-!
# The remaining integer mass of one pair

Traverse the retained count words and cut flags together. A cut flag
skips the corresponding count. Otherwise the interpreter executes
binary addition and trims its result. Stored padding is allowed.
-/

namespace DirectedFlowCutGap.RetainedMassRowProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryArithmetic PackedBooleanConstructor RetainedGridState
open PathCostMaterialization (WordList)

private def additionLabel (pc : Fin 116) : Fin 134 := ⟨18 + pc.val, by omega⟩

def program : Program 134 := fun pc =>
  if pc.val < 18 then
    match pc.val with
    | 0 => .call 1 17 .r3
    | 1 => .branch .r0 2 16 16 4
    | 2 => .make .r0 .nil 3
    | 3 => .ret .r0
    | 4 => .field .r2 .r0 false 5
    | 5 => .field .r3 .r1 false 6
    | 6 => .field .r0 .r0 true 7
    | 7 => .field .r1 .r1 true 8
    | 8 => .call 1 9 .r0
    | 9 => .branch .r3 16 10 3 16
    | 10 => .move .r1 .r0 11
    | 11 => .move .r0 .r2 12
    | 12 => .call (additionLabel 114) 3 .r0
    | _ => .halt
  else if pc.val = 133 then .ret .r3
  else ReferenceProgramLabels.instruction additionLabel
    (CanonicalArithmeticProgram.program ⟨pc.val - 18, by omega⟩)

private theorem addition_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc ≠ .halt) :
    program (additionLabel pc) =
      ReferenceProgramLabels.instruction additionLabel (CanonicalArithmeticProgram.program pc) := by
  by_cases he : pc.val = 115
  · have eq : pc = 115 := Fin.ext he
    subst pc
    exact (h rfl).elim
  · simp [program, additionLabel, show ¬18+pc.val<18 by omega, show 18+pc.val≠133 by omega]

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 134))
    (tape : Bits) (pc : Fin 134) : NaturalState 134 :=
  ⟨heap, heap.length, r, stack, pc, tape⟩

def sum : List Bits → Bits → Bits
  | w :: ws, cut :: cs => if cut then sum ws cs else (addCanonical w (sum ws cs)).1
  | _, _ => []

def steps : List Bits → Bits → ℕ
  | w :: ws, cut :: cs =>
    steps ws cs + (if cut then 8 else 12 + CanonicalArithmeticProgram.instructions false w (sum ws cs))
  | _, _ => 3

private theorem join {a b c : NaturalState 134} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m + n) a (es ++ fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem add_return {heap : NaturalHeap} {a b : ℕ} {x y : Bits}
    (hx : BoolList heap a x) (hy : BoolList heap b y) (c d : ℕ)
    (caller : Frame ℕ 134) (stack : List (Frame ℕ 134)) (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (addCanonical x y).1 ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions false x y + 1)
        (state heap ⟨a,b,c,d⟩ (caller :: stack) tape (additionLabel 114)) []
        (state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let start := CanonicalArithmeticProgram.state heap heap.length a b c d [] tape 114
  obtain ⟨ext, root, _, run, rep⟩ := CanonicalArithmeticProgram.canonical_high false start rfl rfl hx hy rfl
  have lift := ReferenceProgramLabels.run additionLabel CanonicalArithmeticProgram.program program addition_slots run
  have lift := ReferenceProgramStack.run program (caller :: stack) lift
  let s0 := state heap ⟨a,b,c,d⟩ (caller :: stack) tape (additionLabel 114)
  let before := state (heap ++ ext) ⟨a,b,c,root⟩ (caller :: stack) tape (additionLabel 115)
  let after := state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (CanonicalArithmeticProgram.instructions false x y) s0 [] before := by
    simpa [s0,before,start,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      CanonicalArithmeticProgram.state] using lift
  have ret : tickNatural program before = some ⟨after,[],0⟩ := rfl
  rw [CanonicalArithmeticProgram.result_exact false] at rep
  exact ⟨ext,root,rep,join body (NaturalRun.step ret (.done after))⟩

theorem sum_subroutine {heap : NaturalHeap} {a b : ℕ} {words : List Bits} {mask : Bits}
    (hw : WordList heap a words) (hm : BoolList heap b mask) (sameLength : words.length = mask.length)
    (c d : ℕ) (caller : Frame ℕ 134) (stack : List (Frame ℕ 134)) (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (sum words mask) ∧
      NaturalRun program (steps words mask)
        (state heap ⟨a,b,c,d⟩ (caller :: stack) tape 1) []
        (state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction hw generalizing b mask c d caller stack with
  | @nil a hp =>
    have h0 : mask = [] := List.length_eq_zero_iff.mp sameLength.symm
    subst mask
    let saved := caller :: stack
    let fresh := heap.length
    let grown := heap ++ [.nil]
    let base : Registers ℕ := ⟨a,b,c,d⟩
    let s1 := state heap base saved tape 1
    let s2 := state heap base saved tape 2
    let s3 := state grown ⟨fresh,b,c,d⟩ saved tape 3
    let final := state grown (caller.saved.set caller.destination fresh) stack tape caller.continuation
    have h1 : tickNatural program s1 = some ⟨s2,[],0⟩ := by
      simp [s1,s2,base,tickNatural,program,state,Registers.get,tagBranch,hp]
    have h2 : tickNatural program s2 = some ⟨s3,[],0⟩ := by
      simp [s2,s3,grown,base,fresh,tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
    have h3 : tickNatural program s3 = some ⟨final,[],0⟩ := by
      simp [s3,final,saved,tickNatural,program,state,Registers.get]
    exact ⟨[.nil],fresh,.nil (by simp [fresh]),.step h1 (.step h2 (.step h3 (.done final)))⟩
  | @cons a ah atail w ws hp hhead _ ih =>
    cases hm with
    | nil => simp at sameLength
    | @cons b bh btail cut cs hmask hflag hrest =>
      let saved := caller :: stack
      let s1 := state heap ⟨a,b,c,d⟩ saved tape 1
      let s4 := state heap ⟨a,b,c,d⟩ saved tape 4
      let s5 := state heap ⟨a,b,ah,d⟩ saved tape 5
      let s6 := state heap ⟨a,b,ah,bh⟩ saved tape 6
      let s7 := state heap ⟨atail,b,ah,bh⟩ saved tape 7
      let args : Registers ℕ := ⟨atail,btail,ah,bh⟩
      let s8 := state heap args saved tape 8
      let frame : Frame ℕ 134 := ⟨9,.r0,args⟩
      have h1 : tickNatural program s1 = some ⟨s4,[],0⟩ := by
        simp [s1,s4,tickNatural,program,state,Registers.get,tagBranch,hp]
      have h4 : tickNatural program s4 = some ⟨s5,[],0⟩ := by
        simp [s4,s5,tickNatural,program,state,Registers.get,Registers.set,hp]
      have h5 : tickNatural program s5 = some ⟨s6,[],0⟩ := by
        simp [s5,s6,tickNatural,program,state,Registers.get,Registers.set,hmask]
      have h6 : tickNatural program s6 = some ⟨s7,[],0⟩ := by
        simp [s6,s7,tickNatural,program,state,Registers.get,Registers.set,hp]
      have h7 : tickNatural program s7 = some ⟨s8,[],0⟩ := by
        simp [s7,s8,args,tickNatural,program,state,Registers.get,Registers.set,hmask]
      have h8 : tickNatural program s8 = some ⟨state heap args (frame :: saved) tape 1,[],0⟩ := rfl
      obtain ⟨ext, tail, htail, hrun⟩ := ih hrest (by simpa using sameLength) ah bh frame saved
      let grown := heap ++ ext
      let s9 := state grown ⟨tail,btail,ah,bh⟩ saved tape 9
      change NaturalRun program (steps ws cs) (state heap args (frame :: saved) tape 1) [] s9 at hrun
      have headRun : NaturalRun program (steps ws cs + 6) s1 [] s9 :=
        .step h1 (.step h4 (.step h5 (.step h6 (.step h7 (.step h8 hrun)))))
      have hflag' : grown[bh]? = some (.flag cut) := lookup_extend hflag ext
      cases cut with
      | true =>
        let s3 := state grown ⟨tail,btail,ah,bh⟩ saved tape 3
        let final := state grown (caller.saved.set caller.destination tail) stack tape caller.continuation
        have h9 : tickNatural program s9 = some ⟨s3,[],0⟩ := by
          simp [s9,s3,tickNatural,program,state,Registers.get,tagBranch,hflag']
        have h3 : tickNatural program s3 = some ⟨final,[],0⟩ := by
          simp [s3,final,saved,tickNatural,program,state,Registers.get]
        have suffix : NaturalRun program 2 s9 [] final := .step h9 (.step h3 (.done final))
        exact ⟨ext,tail,htail,join headRun suffix⟩
      | false =>
        let s10 := state grown ⟨tail,btail,ah,bh⟩ saved tape 10
        let s11 := state grown ⟨tail,tail,ah,bh⟩ saved tape 11
        let addArgs : Registers ℕ := ⟨ah,tail,ah,bh⟩
        let s12 := state grown addArgs saved tape 12
        let call : Frame ℕ 134 := ⟨3,.r0,addArgs⟩
        let enter := state grown addArgs (call :: saved) tape (additionLabel 114)
        have h9 : tickNatural program s9 = some ⟨s10,[],0⟩ := by
          simp [s9,s10,tickNatural,program,state,Registers.get,tagBranch,hflag']
        have h10 : tickNatural program s10 = some ⟨s11,[],0⟩ := rfl
        have h11 : tickNatural program s11 = some ⟨s12,[],0⟩ := rfl
        have h12 : tickNatural program s12 = some ⟨enter,[],0⟩ := rfl
        obtain ⟨more, root, hsum, hadd⟩ :=
          add_return (boolList_extend hhead ext) htail ah bh call saved tape
        let next := grown ++ more
        let s3 := state next ⟨root,tail,ah,bh⟩ saved tape 3
        let final := state next (caller.saved.set caller.destination root) stack tape caller.continuation
        change NaturalRun program (CanonicalArithmeticProgram.instructions false w (sum ws cs) + 1)
          enter [] s3 at hadd
        have h3 : tickNatural program s3 = some ⟨final,[],0⟩ := by
          simp [s3,final,saved,tickNatural,program,state,Registers.get]
        have hs := NaturalRun.step h9 (.step h10 (.step h11 (.step h12 (join hadd (.step h3 (.done final))))))
        have full := join headRun hs
        refine ⟨ext ++ more, root, ?_, ?_⟩
        · simpa only [sum, Bool.false_eq_true, ite_false, grown, List.append_assoc] using hsum
        · let k := CanonicalArithmeticProgram.instructions false w (sum ws cs)
          change NaturalRun program (steps ws cs + 6 + (k+1+(0+1)+1+1+1+1)) s1 [] final at full
          have hc : steps (w :: ws) (false :: cs) = steps ws cs + 6 + (k+1+(0+1)+1+1+1+1) := by
            simp only [steps, Bool.false_eq_true, ite_false, k]
            omega
          rw [hc]
          simpa only [s1,final,next,grown,List.append_assoc] using full

theorem sum_value (words : List Bits) (mask : Bits) :
    value (sum words mask) = (List.zipWith (fun w b => if b then 0 else value w) words mask).sum := by
  induction words generalizing mask with
  | nil => cases mask <;> rfl
  | cons w ws ih =>
    cases mask with
    | nil => rfl
    | cons b bs =>
      cases b <;> simp [sum,canonical_values,ih]

theorem result_width (words : List Bits) (mask : Bits) (B : ℕ)
    (hw : ∀ w ∈ words, w.length ≤ B) : (sum words mask).length ≤ B + words.length := by
  induction words generalizing mask with
  | nil => cases mask <;> simp [sum]
  | cons w ws ih =>
    cases mask with
    | nil => simp [sum]
    | cons cut cs =>
      have hh := hw w List.mem_cons_self
      have ht := ih cs (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      have hs : (addCanonical w (sum ws cs)).1.length ≤ max w.length (sum ws cs).length + 1 :=
        (trim_spec (add false w (sum ws cs)).1).2.2.1.trans (add_spec false w (sum ws cs)).2.1
      have hmax : max w.length (sum ws cs).length ≤ B + ws.length :=
        max_le (hh.trans (Nat.le_add_right _ _)) ht
      cases cut
      · simp only [sum, Bool.false_eq_true, ite_false, List.length_cons]
        omega
      · simp only [sum, ite_true, List.length_cons]
        omega

def instructionBudget (n B : ℕ) : ℕ := n * (12 + 200 * (2*B+n+2)^2) + 4

private theorem steps_bound_of (words : List Bits) (mask : Bits) (B N : ℕ)
    (hN : words.length ≤ N) (hw : ∀ w ∈ words, w.length ≤ B) :
    steps words mask ≤ words.length * (12 + 200 * (2*B+N+2)^2) + 3 := by
  induction words generalizing mask with
  | nil => cases mask <;> simp [steps]
  | cons w ws ih =>
    cases mask with
    | nil =>
      simp [steps]
    | cons b bs =>
      have subWidth : ∀ y ∈ ws, y.length ≤ B := fun y hy => hw y (List.mem_cons_of_mem _ hy)
      have hsub : ws.length ≤ N := by simp only [List.length_cons] at hN; omega
      have htail := ih bs hsub subWidth
      have hsum := result_width ws bs B subWidth
      have hh := hw w List.mem_cons_self
      have hsize : w.length + (sum ws bs).length + 2 ≤ 2*B+N+2 := by omega
      have hAdd := (CanonicalArithmeticProgram.instructions_bound false w (sum ws bs)).trans
        (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hsize 2))
      simp only [steps, List.length_cons, Nat.add_mul, Nat.one_mul]
      split <;> omega

theorem steps_le (words : List Bits) (mask : Bits) (B : ℕ)
    (hw : ∀ w ∈ words, w.length ≤ B) :
    steps words mask + 1 ≤ instructionBudget words.length B := by
  simpa only [instructionBudget, Nat.add_assoc] using
    Nat.add_le_add_right (steps_bound_of words mask B words.length le_rfl hw) 1

theorem natural_trace {heap : NaturalHeap} {r : Registers ℕ} {words : List Bits} {mask : Bits}
    (hw : WordList heap r.a words) (hm : BoolList heap r.b mask) (lengths : words.length = mask.length)
    (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (sum words mask) ∧
      NaturalRun program (steps words mask + 1) (state heap r [] tape 0) []
        (state (heap ++ ext) (r.set .r3 root) [] tape 17) := by
  let frame : Frame ℕ 134 := ⟨17,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := sum_subroutine hw hm lengths r.c r.d frame [] tape
  have hcall : tickNatural program (state heap r [] tape 0) = some ⟨state heap r [frame] tape 1,[],0⟩ := rfl
  exact ⟨ext,root,hrep,NaturalRun.step hcall hrun⟩

private theorem zip_values (words : List Bits) (mask : Bits) :
    List.zipWith (fun w b => if b then 0 else value w) words mask =
      List.zipWith (fun w b => if b then 0 else w) (words.map value) mask := by
  induction words generalizing mask with
  | nil => cases mask <;> rfl
  | cons w ws ih =>
    cases mask with
    | nil => rfl
    | cons b bs => simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem row_value {n : ℕ} (weights : Row n) (mask : Flags n) (words : List Bits)
    (hdata : words.map value = weights.toList) :
    value (sum words mask.toList) = ∑ i : Fin n, (if mask[i.val] then 0 else weights[i.val]) := by
  rw [sum_value, zip_values, hdata]
  let field (i : Fin n) := if mask[i.val] then 0 else weights[i.val]
  have hs : List.zipWith (fun w b => if b then 0 else w) weights.toList mask.toList = List.ofFn field := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_zipWith, List.getElem_ofFn, Vector.getElem_toList, field]
  rw [hs, List.sum_ofFn]

private theorem at_entry (s : NaturalState 134) (hp : s.pc=0) (hc : s.stack=[])
    (hd : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem retained_row_mass {n H A B : ℕ} {initial : BitState 134}
    (weights : Row n) (mask : Flags n) (words : List Bits)
    (hdata : words.map value = weights.toList) (hwords : ∀ w ∈ words, w.length ≤ B)
    (hs : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hd : (eraseState initial).next=(eraseState initial).heap.length)
    (hw : WordList (eraseState initial).heap (eraseState initial).registers.a words)
    (hm : BoolList (eraseState initial).heap (eraseState initial).registers.b mask.toList) :
    ∃ q out,
      Run program (steps words mask.toList + 1) q initial [] out ∧ (attempt program out).result = none ∧
      (eraseState out).pc=17 ∧ (eraseState out).stack=[] ∧ out.source=initial.source ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (sum words mask.toList) ∧
      value (sum words mask.toList) = (∑ i : Fin n, (if mask[i.val] then 0 else weights[i.val])) ∧
      (sum words mask.toList).length ≤ B+n ∧
      (∃ ext, (eraseState out).heap=(eraseState initial).heap ++ ext) ∧
      q + (attempt program out).operations ≤ completeBound 134 H A (instructionBudget n B) := by
  let input := eraseState initial
  have hlen : words.length = n := by
    simpa only [List.length_map,Vector.length_toList] using congrArg List.length hdata
  obtain ⟨ext,root,hrep,htrace⟩ := natural_trace hw hm (by simp [hlen]) input.source
  have hnil : input.stack = [] := by simp [input,eraseState,State.map,hc]
  have he := at_entry input hp hnil hd
  let final := state (input.heap ++ ext) (input.registers.set .r3 root) [] input.source 17
  have hrun : NaturalRun program (steps words mask.toList + 1) input [] final := by
    rw [he]
    exact htrace
  have halt : tickNatural program final = none := rfl
  obtain ⟨q,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation hs hrun halt
  refine ⟨q,out,hactual,hstop,?_,?_,htape,?_,row_value weights mask words hdata,
    by simpa only [hlen] using result_width words mask.toList B hwords, ⟨ext,?_⟩,hcharge.trans ?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · have hk : steps words mask.toList + 1 ≤ instructionBudget n B := by
      simpa only [hlen] using steps_le words mask.toList B hwords
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.RetainedMassRowProgram
