import DirectedFlowCutGap.CapacityBottleneckProgram

namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def headItems (next : ℕ) (x : Slot) (ys : List RetainedArgminProgram.Item) : List RetainedArgminProgram.Item :=
  if x.enabled then ⟨x.score,x.vertexRoot,next+1⟩::ys else ys

theorem head_return {heap : NaturalHeap} {m b f mt v vt t score tt frame rt : ℕ}
    {x : Slot} {ys : List RetainedArgminProgram.Item}
    (save : heap[frame]?=some (.pair m b)) (context : heap[b]?=some (.pair v t))
    (hm : heap[m]?=some (.pair f mt)) (hf : heap[f]?=some (.flag x.enabled))
    (hv : heap[v]?=some (.pair x.vertexRoot vt)) (ht : heap[t]?=some (.pair score tt))
    (hq : Stored heap score x.score) (tail : RetainedArgminProgram.ItemList heap rt ys)
    (next a c : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 244) (stack : List (Frame ℕ 244)) (source : Bits) :
    ∃ ext root,ext.length=(if x.enabled then 3 else 1) ∧
      NaturalRun program (if x.enabled then 15 else 7)
        (state heap next a c frame rt (⟨pc,.r3,saved⟩::stack) source 211) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RetainedArgminProgram.ItemList (heap++ext) root (headItems next x ys) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair frame rt]
  have t211 : tickNatural program (state heap next a c frame rt frames source 211)=
      some ⟨state (heap++e0) (next+1) a c next rt frames source 212,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e0]
  have t212 : tickNatural program (state (heap++e0) (next+1) a c next rt frames source 212)=
      some ⟨state (heap++e0) (next+1) frame c next rt frames source 213,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,e0,hn]
  have t213 : tickNatural program (state (heap++e0) (next+1) frame c next rt frames source 213)=
      some ⟨state (heap++e0) (next+1) m c next rt frames source 214,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend save e0]
  have t214 : tickNatural program (state (heap++e0) (next+1) m c next rt frames source 214)=
      some ⟨state (heap++e0) (next+1) f c next rt frames source 215,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hm e0]
  have branch : tickNatural program (state (heap++e0) (next+1) f c next rt frames source 215)=
      some ⟨state (heap++e0) (next+1) f c next rt frames source (if x.enabled then 222 else 216),[],0⟩ := by
    cases h : x.enabled <;> simp [tickNatural,program,state,Registers.get,tagBranch,lookup_extend hf e0,h]
  cases h : x.enabled with
  | false =>
    have t216 : tickNatural program (state (heap++e0) (next+1) f c next rt frames source 216)=
        some ⟨state (heap++e0) (next+1) f c next rt frames source 217,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,e0,hn]
    have t217 : tickNatural program (state (heap++e0) (next+1) f c next rt frames source 217)=
        some ⟨state (heap++e0) (next+1) saved.a saved.b saved.c rt stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frames]
    simp only [h,Bool.false_eq_true,ite_false] at branch
    refine ⟨e0,rt,by simp [e0],?_,?_⟩
    · simpa [h,e0] using NaturalRun.step t211 (.step t212 (.step t213 (.step t214
        (.step branch (.step t216 (.step t217 (.done _)))))))
    · simpa [headItems,h] using RetainedArgminProgram.list_extend tail e0
  | true =>
    have t222 : tickNatural program (state (heap++e0) (next+1) f c next rt frames source 222)=
        some ⟨state (heap++e0) (next+1) frame c next rt frames source 223,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,e0,hn]
    have t223 : tickNatural program (state (heap++e0) (next+1) frame c next rt frames source 223)=
        some ⟨state (heap++e0) (next+1) b c next rt frames source 224,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend save e0]
    have t224 : tickNatural program (state (heap++e0) (next+1) b c next rt frames source 224)=
        some ⟨state (heap++e0) (next+1) b v next rt frames source 225,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend context e0]
    have t225 : tickNatural program (state (heap++e0) (next+1) b v next rt frames source 225)=
        some ⟨state (heap++e0) (next+1) b x.vertexRoot next rt frames source 226,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hv e0]
    have t226 : tickNatural program (state (heap++e0) (next+1) b x.vertexRoot next rt frames source 226)=
        some ⟨state (heap++e0) (next+1) t x.vertexRoot next rt frames source 227,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend context e0]
    have t227 : tickNatural program (state (heap++e0) (next+1) t x.vertexRoot next rt frames source 227)=
        some ⟨state (heap++e0) (next+1) score x.vertexRoot next rt frames source 228,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend ht e0]
    have t228 : tickNatural program (state (heap++e0) (next+1) score x.vertexRoot next rt frames source 228)=
        some ⟨state ((heap++e0)++[.pair score x.vertexRoot]) (next+1+1) (next+1) x.vertexRoot next rt frames source 229,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t229 : tickNatural program (state ((heap++e0)++[.pair score x.vertexRoot]) (next+1+1) (next+1) x.vertexRoot next rt frames source 229)=
        some ⟨state ((heap++e0)++[.pair score x.vertexRoot]) (next+1+1) (next+1) x.vertexRoot next rt frames source 230,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,e0,hn,List.append_assoc]
    have t230 : tickNatural program (state ((heap++e0)++[.pair score x.vertexRoot]) (next+1+1) (next+1) x.vertexRoot next rt frames source 230)=
        some ⟨state (((heap++e0)++[.pair score x.vertexRoot])++[.pair (next+1) rt]) (next+1+1+1) (next+1) x.vertexRoot next (next+1+1) frames source 231,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t231 : tickNatural program (state (((heap++e0)++[.pair score x.vertexRoot])++[.pair (next+1) rt]) (next+1+1+1) (next+1) x.vertexRoot next (next+1+1) frames source 231)=
        some ⟨state (((heap++e0)++[.pair score x.vertexRoot])++[.pair (next+1) rt]) (next+1+1+1) saved.a saved.b saved.c (next+1+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frames]
    let ext : NaturalHeap := e0++[.pair score x.vertexRoot,.pair (next+1) rt]
    simp only [h,ite_true] at branch
    refine ⟨ext,next+2,by simp [ext,e0],?_,?_⟩
    · have all := NaturalRun.step t211 (.step t212 (.step t213 (.step t214 (.step branch
        (.step t222 (.step t223 (.step t224 (.step t225 (.step t226 (.step t227
        (.step t228 (.step t229 (.step t230 (.step t231 (.done _)))))))))))))))
      simpa [h,ext,e0,state,List.append_assoc,Nat.add_assoc] using all
    · simp only [headItems,h,ite_true]
      apply RetainedArgminProgram.ItemList.cons (item:=next+1) (tail:=rt)
      · simp [ext,e0,hn]
      · exact ⟨rfl,score,by simp [ext,e0,hn],stored_extend hq ext⟩
      · exact RetainedArgminProgram.list_extend tail ext

end DirectedFlowCutGap.CapacityBottleneck
