import DirectedFlowCutGap.AvoidingZeroContextCalls

namespace DirectedFlowCutGap.AvoidingZeroContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

theorem construct_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits} {sw target : Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs) (metadata : Static heap b adjacency sw target)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 64)
    (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=vs.length+14 ∧ NaturalRun program (5*vs.length+37)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 40) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency
        (List.replicate vs.length BinaryRational.zero) sw target := by
  obtain ⟨ar,ep,sr,tr,hp,he,ha,hs,ht⟩ := metadata
  let frames : List (Frame ℕ 64) := ⟨pc,.r3,saved⟩::stack
  let scratch : Cell ℕ := .pair a b
  let h0 : NaturalHeap := heap++[scratch]
  have hv0 : GraphDiscoveryProgram.Vertices h0 a vs := GraphDiscoveryProgram.vertices_extend vertices _
  obtain ⟨e1,pair,zr,rr,l1,zero,hpair,hrow,_⟩ := zero_return hv0
    (next+1) b next d (by simp [h0,hn]) ⟨a,b,next,d⟩ 42 frames source
  let h1 := h0++e1
  let n1 := next+1+e1.length
  have hn1 : n1=h1.length := by simp [n1,h1,h0,hn];omega
  have hp1 : h1[b]?=some (.pair ar ep) := lookup_extend (lookup_extend hp _) _
  have he1 : h1[ep]?=some (.pair sr tr) := lookup_extend (lookup_extend he _) _
  have hs1 : BoolList h1 sr sw := boolList_extend (boolList_extend hs _) _
  have ht1 : BoolList h1 tr target := boolList_extend (boolList_extend ht _) _
  have ha1 : GraphAdjacencyProgram.Matrix h1 ar adjacency :=
    GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend ha _) _
  have hv1 : GraphDiscoveryProgram.Vertices h1 a vs :=
    GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend vertices _) _
  have hsave : h1[next]?=some scratch := lookup_extend (by simp [h0,hn]) _
  have t40 : tickNatural program (state heap next a b c d frames source 40)=
      some ⟨state h0 (next+1) a b next d frames source 41,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
  have t41 : tickNatural program (state h0 (next+1) a b next d frames source 41)=
      some ⟨state h0 (next+1) a b next d (⟨42,.r3,⟨a,b,next,d⟩⟩::frames) source 28,[],0⟩ := rfl
  have first := NaturalRun.step t40 (.step t41 zero)
  let h2 := h1++[.pair ar rr]
  let h3 := h2++[.pair ep n1]
  have input : AvoidingGraphContext.Input h3 (n1+1) adjacency
      (List.replicate vs.length BinaryRational.zero) sw target := by
    refine ⟨ep,sr,tr,n1,ar,rr,?_,lookup_extend (lookup_extend he1 _) _,?_,
      boolList_extend (boolList_extend hs1 _) _,boolList_extend (boolList_extend ht1 _) _,
      GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend ha1 _) _,
      list_extend (list_extend hrow _) _⟩
    · simp [h3,h2,hn1]
    · simp [h3,h2,hn1]
  obtain ⟨e2,root,l2,context,rep⟩ := context_return
    (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend hv1 _) _) input
    (n1+2) next n1 (by simp [hn1]) ⟨a,n1+1,next,n1⟩ 49 frames source
  have t42 : tickNatural program (state h1 n1 a b next pair frames source 42)=
      some ⟨state h1 n1 a b next rr frames source 43,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hpair,h1]
  have t43 : tickNatural program (state h1 n1 a b next rr frames source 43)=
      some ⟨state h1 n1 ar b next rr frames source 44,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
  have t44 : tickNatural program (state h1 n1 ar b next rr frames source 44)=
      some ⟨state h2 (n1+1) ar b next n1 frames source 45,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2]
  have hp2 : h2[b]?=some (.pair ar ep) := lookup_extend hp1 _
  have t45 : tickNatural program (state h2 (n1+1) ar b next n1 frames source 45)=
      some ⟨state h2 (n1+1) ep b next n1 frames source 46,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp2]
  have t46 : tickNatural program (state h2 (n1+1) ep b next n1 frames source 46)=
      some ⟨state h3 (n1+2) ep (n1+1) next n1 frames source 47,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h3,Nat.add_assoc]
  have hsave3 : h3[next]?=some scratch := lookup_extend (lookup_extend hsave _) _
  have t47 : tickNatural program (state h3 (n1+2) ep (n1+1) next n1 frames source 47)=
      some ⟨state h3 (n1+2) a (n1+1) next n1 frames source 48,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hsave3,scratch]
  have t48 : tickNatural program (state h3 (n1+2) a (n1+1) next n1 frames source 48)=
      some ⟨state h3 (n1+2) a (n1+1) next n1 (⟨49,.r3,⟨a,n1+1,next,n1⟩⟩::frames) source 18,[],0⟩ := rfl
  have t49 : tickNatural program (state (h3++e2) (n1+2+e2.length) a (n1+1) next root frames source 49)=
      some ⟨state (h3++e2) (n1+2+e2.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  have last := run_append context (.step t49 (.done _))
  have middle := NaturalRun.step t42 (.step t43 (.step t44 (.step t45 (.step t46 (.step t47 (.step t48 last))))))
  have all := run_append first middle
  refine ⟨[scratch]++e1++[.pair ar rr,.pair ep n1]++e2,root,?_,?_,?_⟩
  · simp [l1,l2]
  · convert all using 1 <;>
      simp [state,h3,h2,h1,h0,n1,List.append_assoc,Nat.add_assoc]; omega
  · simpa [h3,h2,h1,h0,List.append_assoc] using rep
end DirectedFlowCutGap.AvoidingZeroContext
