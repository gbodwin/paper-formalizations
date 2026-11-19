import DirectedFlowCutGap.RawGraphControllerLaw
import DirectedFlowCutGap.OriginalStoreInitial

/-! Pack the original adjacency rows and binary input words with paid allocations. -/

namespace DirectedFlowCutGap.RawGraphInputStore

open BinaryArithmetic ImmutableReferenceSimulation
open RetainedGridState (PairFlags)
open PackedWordPairTable
open PackedOriginalStore (matrixInto matrixInto_spec extends_matrix rowBits)

def cells (matrix : List Bits) (count level trials : Bits) : ℕ :=
  11+2*(matrix.length+rowBits matrix+count.length+level.length+trials.length)

def prepare (matrix : List Bits) (count level trials : Bits) (tape : Bits) : BitState 26704 × ℕ :=
  let m := matrixInto matrix seed
  let n := word count m
  let l := word level n
  let one := word [true] l
  let values := allocate (.pair l.root one.root) one
  let dims := allocate (.pair n.root values.root) values
  let graph := allocate (.pair m.root dims.root) dims
  let trial := word trials graph
  (⟨trial.heap,trial.next,⟨graph.root,trial.root,[],[]⟩,[],0,tape⟩,trial.operations+16)

theorem exact_cells (matrix : List Bits) (count level trials : Bits) (tape : Bits) :
    (prepare matrix count level trials tape).1.heap.length=cells matrix count level trials := by
  let m := matrixInto matrix seed
  let n := word count m
  let l := word level n
  let one := word [true] l
  let f := allocate (.pair l.root one.root) one
  let dims := allocate (.pair n.root f.root) f
  let graph := allocate (.pair m.root dims.root) dims
  have mSpec := matrixInto_spec matrix seed_spec.bound
  have nSpec := word_spec count mSpec.bound
  have lSpec := word_spec level nSpec.bound
  have oSpec := word_spec [true] lSpec.bound
  have ed := (allocate_extends (.pair l.root one.root) one).trans (allocate_extends (.pair n.root f.root) f)
  have ef := (allocate_extends (.pair l.root one.root) one)
  have fBound : StateBound f := allocate_bound oSpec.bound
    ⟨lSpec.bound.root_width.trans oSpec.extension.length_le,oSpec.bound.root_width⟩
  have nGrow := (lSpec.extension.trans oSpec.extension).trans ef
  have dBound : StateBound dims := allocate_bound fBound
    ⟨nSpec.bound.root_width.trans nGrow.length_le,fBound.root_width⟩
  have mGrow := (nSpec.extension.trans lSpec.extension).trans (oSpec.extension.trans ed)
  have gBound : StateBound graph := allocate_bound dBound
    ⟨mSpec.bound.root_width.trans mGrow.length_le,dBound.root_width⟩
  have tSpec := word_spec trials gBound
  change (word trials graph).heap.length=_
  rw [tSpec.length]
  simp only [graph,dims,f,allocate_length]
  have hm : m.heap.length=2+2*matrix.length+2*rowBits matrix := by
    simpa only [m,seed_spec.length,List.length_nil,storedBits_nil,Nat.mul_zero,Nat.add_zero,Nat.reduceAdd] using mSpec.length
  have hn : n.heap.length=m.heap.length+1+2*count.length := nSpec.length
  have hl : l.heap.length=n.heap.length+1+2*level.length := lSpec.length
  have ho : one.heap.length=l.heap.length+3 := by simpa [one,l] using oSpec.length
  unfold cells
  omega

set_option maxHeartbeats 1100000 in
theorem prepare_spec {n L : ℕ} (adj : PairFlags n) (trials tape : Bits) :
    let matrix := GraphRelaxationRefinement.matrix adj
    let count := n.bits
    let level := L.bits
    let countCells := cells matrix count level trials
    let data := prepare matrix count level trials tape
    RawGraphControllerLaw.Input (L:=L) adj trials (countCells+1) countCells data.1 ∧
    data.2≤64*countCells^3+16 := by
  dsimp only
  let matrix := GraphRelaxationRefinement.matrix adj
  let m := matrixInto matrix seed
  let count := word n.bits m
  let level := word L.bits count
  let one := word [true] level
  let fields := allocate (.pair level.root one.root) one
  let dims := allocate (.pair count.root fields.root) fields
  let graph := allocate (.pair m.root dims.root) dims
  let trial := word trials graph
  let N := cells matrix n.bits L.bits trials
  let whole := (prepare matrix n.bits L.bits trials tape).1
  have matrixSpec := matrixInto_spec matrix seed_spec.bound
  have countSpec := word_spec n.bits matrixSpec.bound
  have levelSpec := word_spec L.bits countSpec.bound
  have oneSpec := word_spec [true] levelSpec.bound
  have eF : Extends one.heap fields.heap := allocate_extends _ _
  have eD : Extends fields.heap dims.heap := allocate_extends _ _
  have eG : Extends dims.heap graph.heap := allocate_extends _ _
  have fBound : StateBound fields := allocate_bound oneSpec.bound
    ⟨levelSpec.bound.root_width.trans oneSpec.extension.length_le,oneSpec.bound.root_width⟩
  have countToFields := (levelSpec.extension.trans oneSpec.extension).trans eF
  have dBound : StateBound dims := allocate_bound fBound
    ⟨countSpec.bound.root_width.trans countToFields.length_le,fBound.root_width⟩
  have matrixToDims := (countSpec.extension.trans countToFields).trans eD
  have gBound : StateBound graph := allocate_bound dBound
    ⟨matrixSpec.bound.root_width.trans matrixToDims.length_le,dBound.root_width⟩
  have trialSpec := word_spec trials gBound
  have matrixToEnd : Extends m.heap trial.heap := (matrixToDims.trans eG).trans trialSpec.extension
  have eDend := eG.trans trialSpec.extension
  have eFend := eD.trans eDend
  have eOneEnd := eF.trans eFend
  have next := trialSpec.bound.next_value
  have length : trial.heap.length=N := exact_cells matrix n.bits L.bits trials tape
  have layout : InitialGraphContexts.Input (L:=L) (eraseState whole).heap (eraseState whole).registers.a adj := by
    change InitialGraphContexts.Input (L:=L) (eraseHeap trial.heap) (value graph.root) adj
    refine ⟨value m.root,value dims.root,value count.root,value fields.root,value level.root,value one.root,
      ?_,?_,?_,extends_matrix matrixToEnd matrixSpec.representation,
      (countToFields.trans eFend).word countSpec.representation,
      (oneSpec.extension.trans eOneEnd).word levelSpec.representation,
      eOneEnd.word oneSpec.representation⟩
    · exact trialSpec.extension.lookup (allocate_lookup dBound (.pair m.root dims.root))
    · exact eDend.lookup (allocate_lookup fBound (.pair count.root fields.root))
    · exact eFend.lookup (allocate_lookup oneSpec.bound (.pair level.root one.root))
  have bounded : whole.Bounded (N+1) N := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · change trial.heap.length+0+1≤N+1
      omega
    · exact length ▸ trialSpec.bound.next_width
    · exact length ▸ trialSpec.bound.heap_bound
    · have graphWidth := gBound.root_width.trans (trialSpec.extension.length_le.trans_eq length)
      have trialWidth := trialSpec.bound.root_width.trans_eq length
      simpa [whole,prepare,trial,graph,dims,fields,one,level,count,m,Registers.All] using
        (show graph.root.length≤N ∧ trial.root.length≤N ∧ ([] : Bits).length≤N ∧ ([] : Bits).length≤N from
          ⟨graphWidth,trialWidth,Nat.zero_le _,Nat.zero_le _⟩)
    · simp [whole,prepare]
  refine ⟨⟨bounded,rfl,rfl,?_,layout,trialSpec.representation⟩,?_⟩
  · simpa only [whole,prepare,eraseState,State.map,List.length_map] using next
  · exact Nat.add_le_add_right (trialSpec.bound.charge.trans_eq (congrArg (fun q => 64*q^3) length)) 16

end DirectedFlowCutGap.RawGraphInputStore
