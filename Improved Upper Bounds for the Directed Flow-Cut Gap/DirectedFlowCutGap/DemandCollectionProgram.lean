import DirectedFlowCutGap.DemandCollectionData

/-! The literal recursive demand program calls the actual shortest controller
for every demand. It retains the new candidate list and sends that same root to
stable selection. The saved demand occurrence never enters arithmetic. -/
namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def shortestLabel (pc : Fin 1344) : Fin 1604 := ⟨pc.val,by omega⟩
def selectLabel (pc : Fin 194) : Fin 1604 := ⟨pc.val+1344,by omega⟩
def program : Program 1604 := fun pc =>
  if pc.val=1343 then .ret .r3
  else if h : pc.val<1344 then
    ReferenceProgramLabels.instruction shortestLabel (GraphRecoveryController.program ⟨pc.val,h⟩)
  else if h : pc.val<1538 then
    ReferenceProgramLabels.instruction selectLabel (RetainedArgminProgram.program ⟨pc.val-1344,by omega⟩)
  else match pc.val with
  | 1540 => .branch .r0 1541 1603 1603 1543
  | 1541 => .make .r3 .nil 1542
  | 1542 => .ret .r3
  | 1543 => .move .r2 .r0 1544
  | 1544 => .field .r0 .r0 true 1545
  | 1545 => .call 1540 1546 .r3
  | 1546 => .make .r2 (.pair .r2 .r3) 1547
  | 1547 => .field .r0 .r2 false 1548
  | 1548 => .field .r0 .r0 false 1549
  | 1549 => .call 1580 1550 .r3
  | 1550 => .call 1592 1551 .r3
  | 1551 => .branch .r3 1560 1603 1603 1552
  | 1552 => .field .r0 .r2 false 1553
  | 1553 => .make .r0 (.pair .r0 .r3) 1554
  | 1554 => .field .r3 .r3 true 1555
  | 1555 => .make .r0 (.pair .r3 .r0) 1556
  | 1556 => .field .r2 .r2 true 1557
  | 1557 => .make .r3 (.pair .r0 .r2) 1558
  | 1558 => .ret .r3
  | 1560 => .field .r3 .r2 true 1561
  | 1561 => .ret .r3
  | 1580 => .field .r2 .r0 false 1581
  | 1581 => .field .r3 .r0 true 1582
  | 1582 => .field .r0 .r1 true 1583
  | 1583 => .field .r0 .r0 true 1584
  | 1584 => .make .r0 (.pair .r0 .r2) 1585
  | 1585 => .field .r2 .r1 true 1586
  | 1586 => .field .r2 .r2 false 1587
  | 1587 => .make .r0 (.pair .r2 .r0) 1588
  | 1588 => .field .r1 .r1 false 1589
  | 1589 => .make .r0 (.pair .r1 .r0) 1590
  | 1590 => .make .r3 (.pair .r3 .r0) 1591
  | 1591 => .ret .r3
  | 1592 => .move .r1 .r3 1593
  | 1593 => .field .r2 .r0 false 1594
  | 1594 => .field .r0 .r1 true 1595
  | 1595 => .field .r0 .r0 false 1596
  | 1596 => .call 1342 1597 .r3
  | 1597 => .ret .r3
  | 1600 => .call 1540 1601 .r3
  | 1601 => .move .r0 .r3 1522
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1604)) (source : Bits) (pc : Fin 1604) : NaturalState 1604 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem shortest_slots (pc : Fin 1344) (h : GraphRecoveryController.program pc≠.halt) :
    program (shortestLabel pc)=ReferenceProgramLabels.instruction shortestLabel (GraphRecoveryController.program pc) := by
  by_cases hp : pc.val=1343
  · have he : pc=1343 := Fin.ext hp
    subst pc;simp [GraphRecoveryController.program] at h
  · simp [program,shortestLabel,pc.isLt,hp]

theorem select_slots (pc : Fin 194) :
    program (selectLabel pc)=ReferenceProgramLabels.instruction selectLabel (RetainedArgminProgram.program pc) := by
  simp [program,selectLabel,show ¬pc.val+1344=1343 by omega,
    show ¬pc.val+1344<1344 by omega,show pc.val+1344<1538 by omega]

theorem run_append {s u v : NaturalState 1604} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.DemandCollection
