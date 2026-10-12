import DirectedFlowCutGap.CanonicalRationalProductProgram

namespace DirectedFlowCutGap.CanonicalRationalProduct
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem product_return (x y : BinaryRational.Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 132)
    (stack : List (Frame ℕ 132)) (source : Bits) :
    ∃ ext root, ext.length=cells x y ∧
      NaturalRun program (instructions x y)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 116) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.mul x y).1 := by
  obtain ⟨xn,xd,hx,hxn,hxd⟩ := left
  obtain ⟨yn,yd,hy,hyn,hyd⟩ := right
  let frames : List (Frame ℕ 132) := ⟨pc,.r3,saved⟩::stack
  let e0 : NaturalHeap := [.pair a b]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
  obtain ⟨ep,rp,lp,runP,repP⟩ := arithmetic_return true
    (boolList_extend hxn e0) (boolList_extend hyn e0) n0 next d dense0 ⟨xn,yn,next,d⟩ 120 frames source
  let h1 := h0++ep
  let n1 := n0+ep.length
  let e1 : NaturalHeap := [.pair rp next]
  let h2 := h1++e1
  let n2 := n1+1
  have dense1 : n1=h1.length := by simp [n1,h1,dense0]
  have dense2 : n2=h2.length := by simp [n2,h2,e1,dense1]
  obtain ⟨ed,rd,ld,runD,repD⟩ := arithmetic_return true
    (boolList_extend (boolList_extend (boolList_extend hxd e0) ep) e1)
    (boolList_extend (boolList_extend (boolList_extend hyd e0) ep) e1)
    n2 n1 rp dense2 ⟨xd,yd,n1,rp⟩ 127 frames source
  let h3 := h2++ed
  let n3 := n2+ed.length
  let e2 : NaturalHeap := [.pair rp rd]
  let h4 := h3++e2
  let n4 := n3+1
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  have hxh0 : h0[a]?=some (.pair xn xd) := lookup_extend hx e0
  have hyh0 : h0[b]?=some (.pair yn yd) := lookup_extend hy e0
  have hxh2 : h2[a]?=some (.pair xn xd) := lookup_extend (lookup_extend (lookup_extend hx e0) ep) e1
  have hyh2 : h2[b]?=some (.pair yn yd) := lookup_extend (lookup_extend (lookup_extend hy e0) ep) e1
  have orig0 : h0[next]?=some (.pair a b) := by simp [h0,e0,hn]
  have orig2 : h2[next]?=some (.pair a b) := lookup_extend (lookup_extend orig0 ep) e1
  have save2 : h2[n1]?=some (.pair rp next) := by simp [h2,e1,dense1]
  have save3 : h3[n1]?=some (.pair rp next) := lookup_extend save2 ed
  have t116 : tickNatural program (state heap next a b c d frames source 116)=
      some ⟨state h0 n0 a b next d frames source 117,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,n0,e0]
  have t117 : tickNatural program (state h0 n0 a b next d frames source 117)=
      some ⟨state h0 n0 xn b next d frames source 118,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hxh0]
  have t118 : tickNatural program (state h0 n0 xn b next d frames source 118)=
      some ⟨state h0 n0 xn yn next d frames source 119,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hyh0]
  have t119 : tickNatural program (state h0 n0 xn yn next d frames source 119)=
      some ⟨state h0 n0 xn yn next d (⟨120,.r3,⟨xn,yn,next,d⟩⟩::frames) source 110,[],0⟩ := by
    simp [tickNatural,program,state]
  have t120 : tickNatural program (state h1 n1 xn yn next rp frames source 120)=
      some ⟨state h2 n2 xn yn n1 rp frames source 121,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,n2,e1]
  have t121 : tickNatural program (state h2 n2 xn yn n1 rp frames source 121)=
      some ⟨state h2 n2 next yn n1 rp frames source 122,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,save2]
  have t122 : tickNatural program (state h2 n2 next yn n1 rp frames source 122)=
      some ⟨state h2 n2 next b n1 rp frames source 123,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,orig2]
  have t123 : tickNatural program (state h2 n2 next b n1 rp frames source 123)=
      some ⟨state h2 n2 a b n1 rp frames source 124,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,orig2]
  have t124 : tickNatural program (state h2 n2 a b n1 rp frames source 124)=
      some ⟨state h2 n2 xd b n1 rp frames source 125,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hxh2]
  have t125 : tickNatural program (state h2 n2 xd b n1 rp frames source 125)=
      some ⟨state h2 n2 xd yd n1 rp frames source 126,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hyh2]
  have t126 : tickNatural program (state h2 n2 xd yd n1 rp frames source 126)=
      some ⟨state h2 n2 xd yd n1 rp (⟨127,.r3,⟨xd,yd,n1,rp⟩⟩::frames) source 110,[],0⟩ := by
    simp [tickNatural,program,state]
  have t127 : tickNatural program (state h3 n3 xd yd n1 rd frames source 127)=
      some ⟨state h3 n3 rp yd n1 rd frames source 128,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,save3]
  have t128 : tickNatural program (state h3 n3 rp yd n1 rd frames source 128)=
      some ⟨state h4 n4 rp yd n1 n3 frames source 129,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h4,n4,e2]
  have t129 : tickNatural program (state h4 n4 rp yd n1 n3 frames source 129)=
      some ⟨state h4 n4 saved.a saved.b saved.c n3 stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  let ext := e0++ep++e1++ed++e2
  have whole := NaturalRun.step t116 (NaturalRun.step t117 (NaturalRun.step t118 (NaturalRun.step t119 (run_append runP (NaturalRun.step t120 (NaturalRun.step t121 (NaturalRun.step t122 (NaturalRun.step t123 (NaturalRun.step t124 (NaturalRun.step t125 (NaturalRun.step t126 (run_append runD (NaturalRun.step t127 (NaturalRun.step t128 (NaturalRun.step t129 (NaturalRun.done _))))))))))))))))
  refine ⟨ext,n3,?_,?_,?_⟩
  · simp [ext,cells,e0,e1,e2,lp,ld]
    omega
  · convert whole using 1 <;>
      simp [instructions,state,ext,h4,h3,h2,h1,h0,n4,n3,n2,n1,n0,e0,e1,e2,List.append_assoc,Nat.add_assoc]
    all_goals omega
  · have record : h4[n3]?=some (.pair rp rd) := by simp [h4,e2,dense3]
    have nr := boolList_extend (boolList_extend (boolList_extend repP e1) ed) e2
    have dr := boolList_extend repD e2
    have he : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,h0,List.append_assoc]
    rw [he]
    exact ⟨rp,rd,record,nr,dr⟩

end DirectedFlowCutGap.CanonicalRationalProduct
