import DirectedFlowCutGap.MaterializedPathSum
import DirectedFlowCutGap.GraphWalkExtension

/-! Traverse the actual recovered edge list and allocate its source-index spine.
Endpoint words and the old empty tail are shared; no edge-pair address is used
as if it were a word address. -/
namespace DirectedFlowCutGap.RecoveredEdgeProjection
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor GraphWalkExtension

def program : Program 12 := fun pc => match pc.val with
  | 0 => .branch .r0 1 11 11 3
  | 1 => .move .r3 .r0 2
  | 2 => .ret .r3
  | 3 => .field .r1 .r0 false 4
  | 4 => .field .r1 .r1 false 5
  | 5 => .field .r0 .r0 true 6
  | 6 => .call 0 7 .r3
  | 7 => .make .r3 (.pair .r1 .r3) 8
  | 8 => .ret .r3
  | 10 => .call 0 11 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 12)) (source : Bits) (pc : Fin 12) : NaturalState 12 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem run_append {s u v : NaturalState 12} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem project_return {heap : NaturalHeap} {a : ℕ} {es : List (Bits×Bits)}
    (input : EdgeList heap a es) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 12) (stack : List (Frame ℕ 12)) (source : Bits) :
    ∃ ext root,ext.length=es.length ∧ NaturalRun program (7*es.length+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PathCostMaterialization.WordList (heap++ext) root (es.map Prod.fst) := by
  induction input generalizing next b c d saved pc stack with
  | @nil a hp =>
    have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
        some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1)=
        some ⟨state heap next a b c a (⟨pc,.r3,saved⟩::stack) source 2,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t2 : tickNatural program (state heap next a b c a (⟨pc,.r3,saved⟩::stack) source 2)=
        some ⟨state heap next saved.a saved.b saved.c a stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    exact ⟨[],a,rfl,by simpa using NaturalRun.step t0 (.step t1 (.step t2 (.done _))),by simpa using PathCostMaterialization.WordList.nil hp⟩
  | @cons a head tail e es hp he ht ih =>
    obtain ⟨u,v,hhead,hu,_⟩ := he
    let frames := (⟨pc,.r3,saved⟩::stack)
    obtain ⟨ext,root,len,rec,rep⟩ := ih next u c d hn ⟨tail,u,c,d⟩ 7 frames
    have t0 : tickNatural program (state heap next a b c d frames source 0)=
        some ⟨state heap next a b c d frames source 3,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t3 : tickNatural program (state heap next a b c d frames source 3)=
        some ⟨state heap next a head c d frames source 4,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t4 : tickNatural program (state heap next a head c d frames source 4)=
        some ⟨state heap next a u c d frames source 5,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hhead]
    have t5 : tickNatural program (state heap next a u c d frames source 5)=
        some ⟨state heap next tail u c d frames source 6,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t6 : tickNatural program (state heap next tail u c d frames source 6)=
        some ⟨state heap next tail u c d (⟨7,.r3,⟨tail,u,c,d⟩⟩::frames) source 0,[],0⟩ := by
      simp [tickNatural,program,state]
    have t7 : tickNatural program (state (heap++ext) (next+ext.length) tail u c root frames source 7)=
        some ⟨state ((heap++ext)++[.pair u root]) (next+ext.length+1) tail u c
          (next+ext.length) frames source 8,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t8 : tickNatural program (state ((heap++ext)++[.pair u root]) (next+ext.length+1) tail u c
        (next+ext.length) frames source 8)=
        some ⟨state ((heap++ext)++[.pair u root]) (next+ext.length+1) saved.a saved.b saved.c
          (next+ext.length) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    have before : NaturalRun program 5 (state heap next a b c d frames source 0) []
        (state heap next tail u c d (⟨7,.r3,⟨tail,u,c,d⟩⟩::frames) source 0) :=
      .step t0 (.step t3 (.step t4 (.step t5 (.step t6 (.done _)))))
    have after : NaturalRun program 2 (state (heap++ext) (next+ext.length) tail u c root frames source 7) []
        (state ((heap++ext)++[.pair u root]) (next+ext.length+1) saved.a saved.b saved.c
          (next+ext.length) stack source pc) := .step t7 (.step t8 (.done _))
    refine ⟨ext++[.pair u root],next+ext.length,by simp [len],?_,?_⟩
    · have all := run_append before (run_append rec after)
      convert all using 1 <;> simp [List.length_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc];omega
    · have dense : next+ext.length=(heap++ext).length := by simp [hn]
      have cell : ((heap++ext)++[.pair u root])[next+ext.length]?=some (.pair u root) := by
        rw [dense];simp
      have result := PathCostMaterialization.WordList.cons cell
        (by simpa only [List.append_assoc] using boolList_extend hu (ext++[.pair u root]))
        (PathCostMaterialization.list_extend rep [.pair u root])
      simpa only [List.map_cons,List.append_assoc] using result

theorem project_high {heap : NaturalHeap} {a : ℕ} {es : List (Bits×Bits)}
    (input : EdgeList heap a es) (next b c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext root,ext.length=es.length ∧ NaturalRun program (7*es.length+4)
      (state heap next a b c d [] source 10) []
      (state (heap++ext) (next+ext.length) a b c root [] source 11) ∧
      PathCostMaterialization.WordList (heap++ext) root (es.map Prod.fst) := by
  obtain ⟨ext,root,len,body,rep⟩ := project_return input next b c d hn ⟨a,b,c,d⟩ 11 [] source
  have first : tickNatural program (state heap next a b c d [] source 10)=
      some ⟨state heap next a b c d [⟨11,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
    simp [tickNatural,program,state]
  exact ⟨ext,root,len,by simpa [state,Nat.add_assoc] using NaturalRun.step first body,rep⟩

end DirectedFlowCutGap.RecoveredEdgeProjection
