import DirectedFlowCutGap.AdaptivePackingActualWeights

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def updatedState {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (q : BinaryFractionalCore.Choice n) : BinaryFractionalCore.State n :=
  ⟨(update capacity s.weights q.mask q.bottleneck).1,selectedRow capacity s q,selectedCost capacity s q,
    (BinaryRational.add s.total (get capacity q.bottleneck)).1,
    (addLoads s.loads q.mask (get capacity q.bottleneck)).1,⟨q,get capacity q.bottleneck⟩::s.events⟩

theorem actual_total_loads {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (data : WeightedData heap frame cap original input label capacity s q)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext, ∃ out : NaturalState 4800,
      NaturalRun program (1+(CanonicalRationalAddition.instructions s.total (get capacity q.bottleneck)+2+
        (30+(PackingLoadRow.steps (get capacity q.bottleneck) s.loads.toList q.mask.toList+57))))
        (state heap next data.selected.old.total data.selected.amount frame data.bestFrame stack source 4519) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=4605 ∧
      PackingStart.StateRecord out.heap out.registers.d label (updatedState capacity s q) := by
  let d := data.selected
  obtain ⟨e₁,total,l₁,r₁,totalRep⟩ := addition_return s.total (get capacity q.bottleneck)
    d.old.totalRep d.amountRep next frame data.bestFrame dense
    ⟨d.old.total,d.amount,frame,data.bestFrame⟩ 4520 stack source
  have call : tickNatural program (state heap next d.old.total d.amount frame data.bestFrame stack source 4519)=
      some ⟨state heap next d.old.total d.amount frame data.bestFrame
        (⟨4520,.r3,⟨d.old.total,d.amount,frame,data.bestFrame⟩⟩::stack) source 4160,[],0⟩ := by
    have slot : program 4519=.call 4160 4520 .r3 := rfl
    simp [tickNatural,state,slot]
  let n₁ := next+e₁.length
  let d₁ := data.extend e₁
  obtain ⟨mp,ap,lp,ep,bp,cp,wp,qp⟩ := d₁.paths
  obtain ⟨e₂,l₂,r₂,tp,ctx⟩ := prepare_loads mp ap lp n₁ d.old.total d.amount total
    (by simp [n₁,List.length_append,dense]) stack source
  let n₂ := n₁+2
  let d₂ := d₁.extend e₂
  have qpath : HeapPath (heap++e₁++e₂) n₁ [true,true,true,true,true,true,false] d.choice :=
    .cons tp (path_extend qp e₂)
  have apath : HeapPath (heap++e₁++e₂) n₁ [true,true,true,true,true,false] d.amount :=
    .cons tp (path_extend ap e₂)
  have epath : HeapPath (heap++e₁++e₂) n₁
      [true,true,true,true,true,true,true,true,false,true,true,true,true,true] d.old.events :=
    .cons tp (path_extend ep e₂)
  have tpath : HeapPath (heap++e₁++e₂) n₁ [false] total := .cons tp (.nil _)
  have cpath : HeapPath (heap++e₁++e₂) n₁ [true,true,false,true] d.cost := .cons tp (path_extend cp e₂)
  have bpath : HeapPath (heap++e₁++e₂) n₁ [true,true,false,false] d.best := .cons tp (path_extend bp e₂)
  have wpath : HeapPath (heap++e₁++e₂) n₁ [true,false] data.weights := .cons tp (path_extend wp e₂)
  obtain ⟨e₃,out,_,r₃,ho,hn,hs,hstack,hpc,rep⟩ := actual_load_output label q
    (update capacity s.weights q.mask q.bottleneck).1 (selectedRow capacity s q) s.loads
    (selectedCost capacity s q) (BinaryRational.add s.total (get capacity q.bottleneck)).1
    (get capacity q.bottleneck) s.events (d:=total)
    qpath apath epath tpath cpath bpath wpath d₂.selected.choiceRep d₂.selected.amountRep d₂.selected.old.eventsRep
    d₂.weightsRep d₂.selected.bestRep d₂.selected.costRep (stored_extend totalRep e₂)
    d₂.selected.old.loadsRep d₂.maskRep ctx n₂
    (by simp [n₂,n₁,List.length_append,dense,l₂,Nat.add_assoc]) stack source
  refine ⟨e₁++e₂++e₃,out,?_,?_,?_,hstack,hs,hpc,rep⟩
  · convert NaturalRun.step call (run_append r₁ (run_append r₂ r₃)) using 1
    · omega
    · rfl
  · simpa [List.append_assoc] using ho
  · simpa [n₂,n₁,List.length_append,l₂,Nat.add_assoc] using hn
end DirectedFlowCutGap.AdaptivePackingState
