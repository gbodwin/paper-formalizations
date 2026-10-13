import DirectedFlowCutGap.AdaptivePackingSelectedData

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

structure WeightedData {n : ℕ} (heap : NaturalHeap) (frame cap original input : ℕ)
    (label : Fin n → Bits) (capacity : Row n) (s : BinaryFractionalCore.State n) (q : BinaryFractionalCore.Choice n) where
  candidateFrame : ℕ
  bestFrame : ℕ
  weights : ℕ
  mask : ℕ
  index : ℕ
  selected : SelectedData heap candidateFrame cap original input label capacity s q
  first : heap[frame]?=some (.pair weights bestFrame)
  second : BestFrame heap bestFrame selected.best selected.cost candidateFrame
  choiceCell : heap[selected.choice]?=some (.pair mask index)
  maskRep : BoolList heap mask q.mask.toList
  weightsRep : StoredList heap weights (update capacity s.weights q.mask q.bottleneck).1.toList

def WeightedData.extend {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (d : WeightedData heap frame cap original input label capacity s q) (ext : NaturalHeap) :
    WeightedData (heap++ext) frame cap original input label capacity s q :=
  ⟨d.candidateFrame,d.bestFrame,d.weights,d.mask,d.index,d.selected.extend ext,
    lookup_extend d.first ext,best_frame_extend d.second ext,lookup_extend d.choiceCell ext,
    boolList_extend d.maskRep ext,list_extend d.weightsRep ext⟩

theorem WeightedData.originalPath {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (d : WeightedData heap frame cap original input label capacity s q) :
    HeapPath heap frame [true,true,true,true,true,true,true,false] original := by
  obtain ⟨_,hp,_⟩ := d.second
  exact .cons d.first (.cons hp (candidate_original_path d.selected.frameRep))

theorem WeightedData.paths {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (d : WeightedData heap frame cap original input label capacity s q) :
    HeapPath heap frame [true,true,true,true,true,false,false] d.mask ∧
    HeapPath heap frame [true,true,true,true,false] d.selected.amount ∧
    HeapPath heap frame [true,true,true,true,true,true,true,false,true,true,true,true,false] d.selected.old.loads ∧
    HeapPath heap frame [true,true,true,true,true,true,true,false,true,true,true,true,true] d.selected.old.events ∧
    HeapPath heap frame [true,false,false] d.selected.best ∧
    HeapPath heap frame [true,false,true] d.selected.cost ∧
    HeapPath heap frame [false] d.weights ∧
    HeapPath heap frame [true,true,true,true,true,false] d.selected.choice := by
  obtain ⟨pm,pa,_,_⟩ := candidate_weight_paths d.selected.frameRep d.selected.old.first d.choiceCell
  obtain ⟨_,hp,hb⟩ := d.second
  have original := d.originalPath
  obtain ⟨nf,hd,af,hn,cf,ha,base,hc,_⟩ := d.selected.frameRep
  refine ⟨.cons d.first (.cons hp pm),.cons d.first (.cons hp pa),
    path_append original d.selected.old.loadsPath,path_append original d.selected.old.eventsPath,
    .cons d.first (.cons hp ?_),.cons d.first (.cons hp ?_),.cons d.first (.nil _),?_⟩
  · exact .cons hb (.nil _)
  · exact .cons hb (.nil _)
  · exact .cons d.first (.cons hp (.cons hd (.cons hn (.cons ha (.cons hc (.nil _))))))
end DirectedFlowCutGap.AdaptivePackingState
