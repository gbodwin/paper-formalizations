import DirectedFlowCutGap.CanonicalRationalSum

/-! A zero load row is allocated by traversing the original stored spine.
The list shares a freshly allocated canonical zero record, not a supplied row. -/
namespace DirectedFlowCutGap.PackingZeroRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def program : Program 16 := fun pc => match pc.val with
  | 0 => .branch .r0 1 13 13 3
  | 1 => .make .r3 .nil 2
  | 2 => .ret .r3
  | 3 => .field .r0 .r0 true 4
  | 4 => .call 0 5 .r3
  | 5 => .make .r3 (.pair .r1 .r3) 6
  | 6 => .ret .r3
  | 8 => .make .r1 .nil 9
  | 9 => .make .r2 (.flag true) 10
  | 10 => .make .r2 (.pair .r2 .r1) 11
  | 11 => .make .r1 (.pair .r1 .r2) 12
  | 12 => .call 0 13 .r3
  | 13 => .make .r3 (.pair .r1 .r3) 14
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 16)) (source : Bits) (pc : Fin 16) : NaturalState 16 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem run_append {s u v : NaturalState 16} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem stored_spine {heap : NaturalHeap} {root : ℕ} {xs : List Fraction}
    (row : StoredList heap root xs) : IndexSpine heap root xs.length := by
  induction row with
  | nil hp => exact .nil hp
  | cons hp _ _ ih => exact .cons hp ih

theorem replicate_return {heap : NaturalHeap} {a b n : ℕ} {x : Fraction}
    (spine : IndexSpine heap a n) (scalar : Stored heap b x)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 16)
    (stack : List (Frame ℕ 16)) (source : Bits) :
    ∃ ext root,ext.length=n+1 ∧ NaturalRun program (5*n+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (List.replicate n x) := by
  induction spine generalizing next c d saved pc stack with
  | @nil a hp =>
    let frames : List (Frame ℕ 16) := ⟨pc,.r3,saved⟩::stack
    have t0 : tickNatural program (state heap next a b c d frames source 0)=
        some ⟨state heap next a b c d frames source 1,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t1 : tickNatural program (state heap next a b c d frames source 1)=
        some ⟨state (heap++[.nil]) (next+1) a b c next frames source 2,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural]
    have t2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 2)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frames]
    exact ⟨[.nil],next,rfl,.step t0 (.step t1 (.step t2 (.done _))),.nil (by simp [hn])⟩
  | @cons a payload tail n hp _ ih =>
    let frames : List (Frame ℕ 16) := ⟨pc,.r3,saved⟩::stack
    obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih next c d hn ⟨tail,b,c,d⟩ 5 frames
    let h1 := heap++et
    let n1 := next+et.length
    let ext := et++[.pair b rt]
    have t0 : tickNatural program (state heap next a b c d frames source 0)=
        some ⟨state heap next a b c d frames source 3,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t3 : tickNatural program (state heap next a b c d frames source 3)=
        some ⟨state heap next tail b c d frames source 4,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t4 : tickNatural program (state heap next tail b c d frames source 4)=
        some ⟨state heap next tail b c d (⟨5,.r3,⟨tail,b,c,d⟩⟩::frames) source 0,[],0⟩ := by
      simp [tickNatural,program,state]
    have t5 : tickNatural program (state h1 n1 tail b c rt frames source 5)=
        some ⟨state (h1++[.pair b rt]) (n1+1) tail b c n1 frames source 6,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
    have t6 : tickNatural program (state (h1++[.pair b rt]) (n1+1) tail b c n1 frames source 6)=
        some ⟨state (h1++[.pair b rt]) (n1+1) saved.a saved.b saved.c n1 stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frames]
    have whole := NaturalRun.step t0 (.step t3 (.step t4 (run_append tailRun (.step t5 (.step t6 (.done _))))))
    refine ⟨ext,n1,by simp [ext,lt],?_,?_⟩
    · convert whole using 1 <;> simp [ext,h1,n1,List.append_assoc,Nat.add_assoc]
    · change StoredList (heap++ext) n1 (x::List.replicate n x)
      rw [show heap++ext=h1++[.pair b rt] by simp [ext,h1,List.append_assoc]]
      exact .cons (by simp [n1,h1,hn]) (stored_extend (stored_extend scalar et) _) (list_extend tailRep _)
end DirectedFlowCutGap.PackingZeroRow
