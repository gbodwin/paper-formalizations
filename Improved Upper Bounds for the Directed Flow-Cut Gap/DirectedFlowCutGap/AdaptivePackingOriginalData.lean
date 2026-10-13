import DirectedFlowCutGap.AdaptivePackingLoadOutput

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- A proof-side view of the original immutable state record, with no new machine data. -/
structure OriginalData {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits)
    (s : BinaryFractionalCore.State n) where
  weights : ℕ
  best : ℕ
  cost : ℕ
  total : ℕ
  loads : ℕ
  events : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ
  first : heap[root]?=some (.pair weights k1)
  second : heap[k1]?=some (.pair best k2)
  third : heap[k2]?=some (.pair cost k3)
  fourth : heap[k3]?=some (.pair total k4)
  fifth : heap[k4]?=some (.pair loads events)
  weightsRep : StoredList heap weights s.weights.toList
  bestRep : StoredList heap best s.best.toList
  costRep : Stored heap cost s.bestCost
  totalRep : Stored heap total s.total
  loadsRep : StoredList heap loads s.loads.toList
  eventsRep : PackingStart.EventList heap label events s.events

theorem original_data {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (h : PackingStart.StateRecord heap root label s) :
    Nonempty (OriginalData heap root label s) := by
  obtain ⟨w,b,c,t,l,e,k1,k2,k3,k4,h1,h2,h3,h4,h5,hw,hb,hc,ht,hl,he⟩ := h
  exact ⟨⟨w,b,c,t,l,e,k1,k2,k3,k4,h1,h2,h3,h4,h5,hw,hb,hc,ht,hl,he⟩⟩

def OriginalData.extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) (ext : NaturalHeap) :
    OriginalData (heap++ext) root label s :=
  ⟨o.weights,o.best,o.cost,o.total,o.loads,o.events,o.k1,o.k2,o.k3,o.k4,
    lookup_extend o.first ext,lookup_extend o.second ext,lookup_extend o.third ext,
    lookup_extend o.fourth ext,lookup_extend o.fifth ext,
    list_extend o.weightsRep ext,list_extend o.bestRep ext,stored_extend o.costRep ext,
    stored_extend o.totalRep ext,list_extend o.loadsRep ext,PackingStart.events_extend o.eventsRep ext⟩

theorem OriginalData.weightsPath {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) :
    HeapPath heap root [false] o.weights := .cons o.first (.nil _)
theorem OriginalData.bestPath {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) :
    HeapPath heap root [true,false] o.best := .cons o.first (.cons o.second (.nil _))
theorem OriginalData.costPath {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) :
    HeapPath heap root [true,true,false] o.cost := .cons o.first (.cons o.second (.cons o.third (.nil _)))
theorem OriginalData.totalPath {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) :
    HeapPath heap root [true,true,true,false] o.total :=
      .cons o.first (.cons o.second (.cons o.third (.cons o.fourth (.nil _))))
theorem OriginalData.loadsPath {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) :
    HeapPath heap root [true,true,true,true,false] o.loads :=
      .cons o.first (.cons o.second (.cons o.third (.cons o.fourth (.cons o.fifth (.nil _)))))
theorem OriginalData.eventsPath {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (o : OriginalData heap root label s) :
    HeapPath heap root [true,true,true,true,true] o.events :=
      .cons o.first (.cons o.second (.cons o.third (.cons o.fourth (.cons o.fifth (.nil _)))))
end DirectedFlowCutGap.AdaptivePackingState
