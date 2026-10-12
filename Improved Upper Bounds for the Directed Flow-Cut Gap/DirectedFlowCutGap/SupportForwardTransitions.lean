import DirectedFlowCutGap.SupportVertexVisit

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem pass_head {heap : NaturalHeap} {a head tail b : ℕ}
    (hp : heap[a]?=some (.pair head tail)) (next c d : ℕ)
    (frames : List (Frame ℕ 280)) (source : Bits) :
    NaturalRun program 4 (state heap next a b c d frames source 220) []
      (state (heap++[.pair a b]) (next+1) head b next d
        (⟨227,.r3,⟨head,b,next,d⟩⟩::frames) source 190) := by
  have t220 : tickNatural program (state heap next a b c d frames source 220)=
      some ⟨state heap next a b c d frames source 224,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,hp,tagBranch]
  have t224 : tickNatural program (state heap next a b c d frames source 224)=
      some ⟨state (heap++[.pair a b]) (next+1) a b next d frames source 225,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t225 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d frames source 225)=
      some ⟨state (heap++[.pair a b]) (next+1) head b next d frames source 226,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp [.pair a b]]
  have t226 : tickNatural program (state (heap++[.pair a b]) (next+1) head b next d frames source 226)=
      some ⟨state (heap++[.pair a b]) (next+1) head b next d
        (⟨227,.r3,⟨head,b,next,d⟩⟩::frames) source 190,[],0⟩ := by
    simp [tickNatural,program,state]
  exact .step t220 (.step t224 (.step t225 (.step t226 (.done _))))

theorem pass_continue {heap : NaturalHeap} {p a b head tail table supp : ℕ}
    (scratch : heap[p]?=some (.pair a b)) (hctx : heap[b]?=some (.pair table supp))
    (hp : heap[a]?=some (.pair head tail)) (next newtable : ℕ)
    (frames : List (Frame ℕ 280)) (source : Bits) :
    NaturalRun program 6 (state heap next head b p newtable frames source 227) []
      (state (heap++[.pair newtable supp]) (next+1) tail next p newtable
        (⟨233,.r3,⟨tail,next,p,newtable⟩⟩::frames) source 220) := by
  let ext : NaturalHeap := [.pair newtable supp]
  have t227 : tickNatural program (state heap next head b p newtable frames source 227)=
      some ⟨state heap next b b p newtable frames source 228,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t228 : tickNatural program (state heap next b b p newtable frames source 228)=
      some ⟨state heap next supp b p newtable frames source 229,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t229 : tickNatural program (state heap next supp b p newtable frames source 229)=
      some ⟨state (heap++ext) (next+1) supp next p newtable frames source 230,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext]
  have t230 : tickNatural program (state (heap++ext) (next+1) supp next p newtable frames source 230)=
      some ⟨state (heap++ext) (next+1) a next p newtable frames source 231,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend scratch ext]
  have t231 : tickNatural program (state (heap++ext) (next+1) a next p newtable frames source 231)=
      some ⟨state (heap++ext) (next+1) tail next p newtable frames source 232,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp ext]
  have t232 : tickNatural program (state (heap++ext) (next+1) tail next p newtable frames source 232)=
      some ⟨state (heap++ext) (next+1) tail next p newtable
        (⟨233,.r3,⟨tail,next,p,newtable⟩⟩::frames) source 220,[],0⟩ := by
    simp [tickNatural,program,state]
  exact .step t227 (.step t228 (.step t229 (.step t230 (.step t231 (.step t232 (.done _))))))

end DirectedFlowCutGap.SupportRecoveryProgram
