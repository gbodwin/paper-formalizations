import DirectedFlowCutGap.PositiveInventoryPrefix

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem zero_advance {heap : NaturalHeap} {a b vh vt cost ct ctx flag : ℕ}
    (hs : heap[ctx]?=some (.pair a b)) (ha : heap[a]?=some (.pair vh vt))
    (hb : heap[b]?=some (.pair cost ct)) (hf : heap[flag]?=some (.flag true))
    (next num : ℕ) (stack : List (Frame ℕ 48)) (source : Bits) :
    NaturalRun program 5 (state heap next num b ctx flag stack source 18) []
      (state heap next vt ct ctx flag stack source 24) := by
  have t0 : tickNatural program (state heap next num b ctx flag stack source 18)=
      some ⟨state heap next num b ctx flag stack source 20,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,hf]
  have t1 : tickNatural program (state heap next num b ctx flag stack source 20)=
      some ⟨state heap next a b ctx flag stack source 21,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs]
  have t2 : tickNatural program (state heap next a b ctx flag stack source 21)=
      some ⟨state heap next vt b ctx flag stack source 22,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ha]
  have t3 : tickNatural program (state heap next vt b ctx flag stack source 22)=
      some ⟨state heap next vt b ctx flag stack source 23,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs]
  have t4 : tickNatural program (state heap next vt b ctx flag stack source 23)=
      some ⟨state heap next vt ct ctx flag stack source 24,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  exact .step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.done _)))))

theorem positive_advance {heap : NaturalHeap} {a b vh vt cost ct ctx flag : ℕ}
    (hs : heap[ctx]?=some (.pair a b)) (ha : heap[a]?=some (.pair vh vt))
    (hb : heap[b]?=some (.pair cost ct)) (hf : heap[flag]?=some (.flag false))
    (next num : ℕ) (stack : List (Frame ℕ 48)) (source : Bits) :
    NaturalRun program 11 (state heap next num b ctx flag stack source 18) []
      (state (heap++[.pair cost vh]) (next+1) vt ct next next stack source 40) := by
  have hs0 := lookup_extend hs [Cell.pair cost vh]
  have ha0 := lookup_extend ha [Cell.pair cost vh]
  have hb0 := lookup_extend hb [Cell.pair cost vh]
  have t0 : tickNatural program (state heap next num b ctx flag stack source 18)=
      some ⟨state heap next num b ctx flag stack source 30,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,hf]
  have t1 : tickNatural program (state heap next num b ctx flag stack source 30)=
      some ⟨state heap next a b ctx flag stack source 31,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs]
  have t2 : tickNatural program (state heap next a b ctx flag stack source 31)=
      some ⟨state heap next vh b ctx flag stack source 32,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ha]
  have t3 : tickNatural program (state heap next vh b ctx flag stack source 32)=
      some ⟨state heap next vh b ctx flag stack source 33,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs]
  have t4 : tickNatural program (state heap next vh b ctx flag stack source 33)=
      some ⟨state heap next vh cost ctx flag stack source 34,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t5 : tickNatural program (state heap next vh cost ctx flag stack source 34)=
      some ⟨state (heap++[.pair cost vh]) (next+1) vh cost ctx next stack source 35,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t6 : tickNatural program (state (heap++[.pair cost vh]) (next+1) vh cost ctx next stack source 35)=
      some ⟨state (heap++[.pair cost vh]) (next+1) a cost ctx next stack source 36,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs0]
  have t7 : tickNatural program (state (heap++[.pair cost vh]) (next+1) a cost ctx next stack source 36)=
      some ⟨state (heap++[.pair cost vh]) (next+1) vt cost ctx next stack source 37,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ha0]
  have t8 : tickNatural program (state (heap++[.pair cost vh]) (next+1) vt cost ctx next stack source 37)=
      some ⟨state (heap++[.pair cost vh]) (next+1) vt b ctx next stack source 38,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs0]
  have t9 : tickNatural program (state (heap++[.pair cost vh]) (next+1) vt b ctx next stack source 38)=
      some ⟨state (heap++[.pair cost vh]) (next+1) vt ct ctx next stack source 39,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
  have t10 : tickNatural program (state (heap++[.pair cost vh]) (next+1) vt ct ctx next stack source 39)=
      some ⟨state (heap++[.pair cost vh]) (next+1) vt ct next next stack source 40,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.done _)))))))))))

end DirectedFlowCutGap.PositiveInventory
