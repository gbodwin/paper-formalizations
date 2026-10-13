import DirectedFlowCutGap.AvoidingShortestCalls

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

def zeroRows (vs : List Bits) : List Fraction := List.replicate vs.length BinaryRational.zero

def result (vs adjacency : List Bits) (sw target : Bits) : Option Walk :=
  GraphRecoveryController.result vs adjacency (zeroRows vs) sw target sw

def steps (vs adjacency : List Bits) (sw target : Bits) : ℕ :=
  5*vs.length+49+GraphRecoveryController.steps vs adjacency (zeroRows vs) sw target sw

def cells (vs adjacency : List Bits) (sw target : Bits) : ℕ :=
  vs.length+15+GraphRecoveryController.cells vs adjacency (zeroRows vs) sw target sw

theorem search_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits} {sw target : Bits}
    (N : ℕ) (input : GraphDiscoveryProgram.Vertices heap a vs)
    (metadata : AvoidingZeroContext.Static heap b adjacency sw target)
    (rows : N≤adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N≤(adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value target<N) (hc : ∀ v∈vs,value v<vs.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency (zeroRows vs) sw target sw=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges sw target).map Prod.fst,value w<vs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1440)
    (stack : List (Frame ℕ 1440)) (source : Bits) :
    ∃ ext root,ext.length=cells vs adjacency sw target ∧ NaturalRun program (steps vs adjacency sw target)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1410) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root (result vs adjacency sw target) := by
  obtain ⟨ar,ep,sr,tr,hp,he,ha,hs,htt⟩ := metadata
  let frames : List (Frame ℕ 1440) := ⟨pc,.r3,saved⟩::stack
  let scratch : Cell ℕ := .pair a b
  let h0 : NaturalHeap := heap++[scratch]
  have hi0 : GraphDiscoveryProgram.Vertices h0 a vs := GraphDiscoveryProgram.vertices_extend input _
  have hm0 : AvoidingZeroContext.Static h0 b adjacency sw target :=
    AvoidingZeroContext.static_extend ⟨ar,ep,sr,tr,hp,he,ha,hs,htt⟩ _
  obtain ⟨e1,contextRoot,l1,zero,context⟩ := zero_return hi0 hm0
    (next+1) next d (by simp [h0,hn]) ⟨a,b,next,d⟩ 1412 frames source
  let h1 := h0++e1
  let n1 := next+1+e1.length
  have hn1 : n1=h1.length := by simp [n1,h1,h0,hn];omega
  have hi1 : GraphDiscoveryProgram.Vertices h1 a vs := GraphDiscoveryProgram.vertices_extend hi0 _
  have hs1 : BoolList h1 sr sw := boolList_extend (boolList_extend hs _) _
  obtain ⟨e2,root,l2,graph,rep⟩ := graph_return N hi1 context hs1 rows cols hv ht
    (by simpa only [List.length_replicate] using hc)
    (by simpa only [zeroRows,List.length_replicate] using valid)
    n1 contextRoot hn1 ⟨a,contextRoot,sr,contextRoot⟩ 1417 frames source
  have t0 : tickNatural program (state heap next a b c d frames source 1410)=
      some ⟨state h0 (next+1) a b next d frames source 1411,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
  have t1 : tickNatural program (state h0 (next+1) a b next d frames source 1411)=
      some ⟨state h0 (next+1) a b next d (⟨1412,.r3,⟨a,b,next,d⟩⟩::frames) source 62,[],0⟩ := rfl
  have first := NaturalRun.step t0 (.step t1 zero)
  have hp1 : h1[b]?=some (.pair ar ep) := lookup_extend (lookup_extend hp _) _
  have he1 : h1[ep]?=some (.pair sr tr) := lookup_extend (lookup_extend he _) _
  have hsave : h1[next]?=some scratch := lookup_extend (by simp [h0,hn]) _
  have t2 : tickNatural program (state h1 n1 a b next contextRoot frames source 1412)=
      some ⟨state h1 n1 a contextRoot next contextRoot frames source 1413,[],0⟩ := rfl
  have t3 : tickNatural program (state h1 n1 a contextRoot next contextRoot frames source 1413)=
      some ⟨state h1 n1 a contextRoot b contextRoot frames source 1414,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hsave,scratch]
  have t4 : tickNatural program (state h1 n1 a contextRoot b contextRoot frames source 1414)=
      some ⟨state h1 n1 a contextRoot ep contextRoot frames source 1415,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
  have t5 : tickNatural program (state h1 n1 a contextRoot ep contextRoot frames source 1415)=
      some ⟨state h1 n1 a contextRoot sr contextRoot frames source 1416,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,he1]
  have t6 : tickNatural program (state h1 n1 a contextRoot sr contextRoot frames source 1416)=
      some ⟨state h1 n1 a contextRoot sr contextRoot
        (⟨1417,.r3,⟨a,contextRoot,sr,contextRoot⟩⟩::frames) source 1406,[],0⟩ := rfl
  have t7 : tickNatural program (state (h1++e2) (n1+e2.length) a contextRoot sr root frames source 1417)=
      some ⟨state (h1++e2) (n1+e2.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  have last := run_append graph (.step t7 (.done _))
  have middle := NaturalRun.step t2 (.step t3 (.step t4 (.step t5 (.step t6 last))))
  have all := run_append first middle
  refine ⟨[scratch]++e1++e2,root,?_,?_,?_⟩
  · simp [cells,zeroRows,l1,l2];omega
  · convert all using 1 <;> simp [steps,zeroRows,state,h1,h0,n1,List.append_assoc,Nat.add_assoc] <;> omega
  · simpa [result,zeroRows,h1,h0,List.append_assoc] using rep
end DirectedFlowCutGap.AvoidingShortest
