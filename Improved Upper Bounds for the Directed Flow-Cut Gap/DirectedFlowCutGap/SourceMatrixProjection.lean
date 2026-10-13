import DirectedFlowCutGap.PackingSourceContracts

/-! An actual recursive first-column projection. The returned matrix spine
contains the original decoded word pointers in original row order. -/
namespace DirectedFlowCutGap.SourceMatrixProjection
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open WordPairTableRead GraphDiscoveryProgram

def program : Program 16 := fun pc => match pc.val with
  | 0 => .branch .r0 1 15 15 4
  | 1 => .make .r3 .nil 2
  | 2 => .ret .r3
  | 4 => .field .r1 .r0 false 5
  | 5 => .field .r1 .r1 false 6
  | 6 => .field .r0 .r0 true 7
  | 7 => .call 0 8 .r3
  | 8 => .make .r3 (.pair .r1 .r3) 9
  | 9 => .ret .r3
  | 14 => .call 0 15 .r3
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

theorem project_return {heap : NaturalHeap} {a : ℕ} {rows : List (Bits × Bits)}
    (table : Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 16) (stack : List (Frame ℕ 16)) (source : Bits) :
    ∃ ext root, ext.length=rows.length+1 ∧
      NaturalRun program (7*rows.length+3)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Vertices (heap++ext) root (rows.map Prod.fst) := by
  induction table generalizing next b c d saved pc stack with
  | @nil root hp =>
    refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
    have t0 : tickNatural program (state heap next root b c d (⟨pc,.r3,saved⟩::stack) source 0)=
        some ⟨state heap next root b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t1 : tickNatural program (state heap next root b c d (⟨pc,.r3,saved⟩::stack) source 1)=
        some ⟨state (heap++[.nil]) (next+1) root b c next (⟨pc,.r3,saved⟩::stack) source 2,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
    have t2 : tickNatural program
        (state (heap++[.nil]) (next+1) root b c next (⟨pc,.r3,saved⟩::stack) source 2)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    exact .step t0 (.step t1 (.step t2 (.done _)))
  | @cons root item tail num den x y rest hp hv hx hy ht ih =>
    obtain ⟨ext,out,len,run,rep⟩ := ih next num c d hn ⟨tail,num,c,d⟩ 8
      (⟨pc,.r3,saved⟩::stack)
    let cell := Cell.pair num out
    have tailRep : Vertices ((heap++ext)++[cell]) out (rest.map Prod.fst) :=
      vertices_extend rep [cell]
    have headRep : BoolList ((heap++ext)++[cell]) num x :=
      boolList_extend (boolList_extend hx ext) [cell]
    have rootRep : ((heap++ext)++[cell])[next+ext.length]?=some cell := by simp [hn]
    refine ⟨ext++[cell],next+ext.length,by simp [len],?_,?_⟩
    · have t0 : tickNatural program
          (state heap next root b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next root b c d (⟨pc,.r3,saved⟩::stack) source 4,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t4 : tickNatural program
          (state heap next root b c d (⟨pc,.r3,saved⟩::stack) source 4)=
          some ⟨state heap next root item c d (⟨pc,.r3,saved⟩::stack) source 5,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t5 : tickNatural program
          (state heap next root item c d (⟨pc,.r3,saved⟩::stack) source 5)=
          some ⟨state heap next root num c d (⟨pc,.r3,saved⟩::stack) source 6,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hv]
      have t6 : tickNatural program
          (state heap next root num c d (⟨pc,.r3,saved⟩::stack) source 6)=
          some ⟨state heap next tail num c d (⟨pc,.r3,saved⟩::stack) source 7,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t7 : tickNatural program
          (state heap next tail num c d (⟨pc,.r3,saved⟩::stack) source 7)=
          some ⟨state heap next tail num c d
            (⟨8,.r3,⟨tail,num,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0,[],0⟩ := by rfl
      have t8 : tickNatural program
          (state (heap++ext) (next+ext.length) tail num c out (⟨pc,.r3,saved⟩::stack) source 8)=
          some ⟨state ((heap++ext)++[cell]) (next+ext.length+1) tail num c
            (next+ext.length) (⟨pc,.r3,saved⟩::stack) source 9,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,cell]
      have t9 : tickNatural program
          (state ((heap++ext)++[cell]) (next+ext.length+1) tail num c
            (next+ext.length) (⟨pc,.r3,saved⟩::stack) source 9)=
          some ⟨state ((heap++ext)++[cell]) (next+ext.length+1) saved.a saved.b saved.c
            (next+ext.length) stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have joined := run_append run (.step t8 (.step t9 (.done _)))
      simpa [List.length_cons,Nat.mul_add,Nat.add_assoc,List.append_assoc] using
        NaturalRun.step t0 (.step t4 (.step t5 (.step t6 (.step t7 joined))))
    · simpa [List.append_assoc] using Vertices.cons rootRep headRep tailRep

end DirectedFlowCutGap.SourceMatrixProjection
