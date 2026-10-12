import DirectedFlowCutGap.GraphRelaxationRefinement

/-! Concrete target handling and table iteration around the actual relaxation
scan. The target-zero record and every new table spine are allocated by code. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

abbrev Entry := GraphRelaxationProgram.Entry
abbrev Table := GraphRelaxationProgram.Table
abbrev StoredOption := GraphRelaxationProgram.StoredOption

def zero : Walk := ⟨[],BinaryRational.zero⟩
def atVertex (adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (old : List Entry) : Option Walk :=
  if BinaryComparisonProgram.order u target=.eq then some zero else
    GraphRelaxationProgram.scan adjacency rows sw u old

def pass (adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (old : List Entry) : List Bits → List Entry
  | [] => []
  | u::us => match atVertex adjacency rows sw target u old with
      | none => pass adjacency rows sw target old us
      | some q => (u,q)::pass adjacency rows sw target old us

def atSteps (adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (old : List Entry) : ℕ := BinaryComparisonProgram.steps u target+6+
  if BinaryComparisonProgram.order u target=.eq then 6 else
    GraphRelaxationProgram.steps adjacency rows sw u old+11

def atCells (adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (old : List Entry) : ℕ := 1+BinaryComparisonProgram.cells u target+
  if BinaryComparisonProgram.order u target=.eq then 5 else
    1+GraphRelaxationProgram.cells adjacency rows sw u old

def passSteps (adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (old : List Entry) : List Bits → ℕ
  | [] => 3
  | u::us => passSteps adjacency rows sw target old us+atSteps adjacency rows sw target u old+
      match atVertex adjacency rows sw target u old with | none => 10 | some _ => 13

def passCells (adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (old : List Entry) : List Bits → ℕ
  | [] => 1
  | u::us => passCells adjacency rows sw target old us+1+atCells adjacency rows sw target u old+
      match atVertex adjacency rows sw target u old with | none => 0 | some _ => 2

/-- A literal retained list of padded vertex words. -/
inductive Vertices (heap : NaturalHeap) : ℕ → List Bits → Prop
  | nil {p} : heap[p]?=some .nil → Vertices heap p []
  | cons {p head tail u us} : heap[p]?=some (.pair head tail) → BoolList heap head u →
      Vertices heap tail us → Vertices heap p (u::us)

def Context (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits) (rows : List Fraction)
    (sw target : Bits) (old : List Entry) : Prop :=
  ∃ tr bundle oldRoot mix matrix cost,heap[p]?=some (.pair tr bundle) ∧
    heap[bundle]?=some (.pair oldRoot mix) ∧ heap[mix]?=some (.pair matrix cost) ∧
    BoolList heap tr target ∧ Table heap oldRoot old ∧
    GraphAdjacencyProgram.Matrix heap matrix adjacency ∧ OutgoingCostProgram.Context heap cost rows sw

theorem vertices_extend {heap : NaturalHeap} {p : ℕ} {us : List Bits}
    (h : Vertices heap p us) (extra : NaturalHeap) : Vertices (heap++extra) p us := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp extra)
  | cons hp hu _ ih => exact .cons (lookup_extend hp extra) (boolList_extend hu extra) ih

theorem context_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits} {rows : List Fraction}
    {sw target : Bits} {old : List Entry} (h : Context heap p adjacency rows sw target old)
    (extra : NaturalHeap) : Context (heap++extra) p adjacency rows sw target old := by
  obtain ⟨tr,bundle,oldRoot,mix,matrix,cost,hp,hb,hm,ht,ho,ha,hc⟩ := h
  exact ⟨tr,bundle,oldRoot,mix,matrix,cost,lookup_extend hp extra,lookup_extend hb extra,
    lookup_extend hm extra,boolList_extend ht extra,GraphRelaxationProgram.table_extend ho extra,
    GraphAdjacencyProgram.matrix_extend ha extra,PathCostMaterialization.context_extend hc extra⟩

def scanLabel (pc : Fin 532) : Fin 720 := ⟨pc.val,by omega⟩
def cmpLabel (pc : Fin 48) : Fin 720 := ⟨pc.val+532,by omega⟩
def program : Program 720 := fun pc =>
  if pc.val=531 ∨ pc.val=579 then .ret .r3
  else if h : pc.val<532 then
    ReferenceProgramLabels.instruction scanLabel (GraphRelaxationProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<580 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val-532,by omega⟩)
  else match pc.val with
  | 580 => .call 532 579 .r3
  | 590 => .make .r3 .nil 591
  | 591 => .make .r0 (.flag true) 592
  | 592 => .make .r0 (.pair .r0 .r3) 593
  | 593 => .make .r2 (.pair .r3 .r0) 594
  | 594 => .make .r3 (.pair .r3 .r2) 595
  | 595 => .ret .r3
  | 600 => .make .r2 (.pair .r0 .r1) 601
  | 601 => .field .r1 .r1 false 602
  | 602 => .call 580 603 .r3
  | 603 => .branch .r3 590 604 604 719
  | 604 => .field .r0 .r2 false 605
  | 605 => .field .r1 .r2 true 606
  | 606 => .field .r1 .r1 true 607
  | 607 => .field .r3 .r1 true 608
  | 608 => .make .r3 (.pair .r0 .r3) 609
  | 609 => .field .r0 .r1 false 610
  | 610 => .move .r1 .r3 611
  | 611 => .call 530 612 .r3
  | 612 => .ret .r3
  | 630 => .branch .r0 631 719 719 633
  | 631 => .make .r3 .nil 632
  | 632 => .ret .r3
  | 633 => .field .r2 .r0 false 634
  | 634 => .field .r0 .r0 true 635
  | 635 => .call 630 636 .r3
  | 636 => .make .r2 (.pair .r2 .r3) 637
  | 637 => .field .r0 .r2 false 638
  | 638 => .call 600 639 .r3
  | 639 => .branch .r3 644 719 719 640
  | 640 => .field .r0 .r2 false 641
  | 641 => .make .r0 (.pair .r0 .r3) 642
  | 642 => .field .r2 .r2 true 643
  | 643 => .make .r3 (.pair .r0 .r2) 645
  | 644 => .field .r3 .r2 true 645
  | 645 => .ret .r3
  | 660 => .branch .r0 661 719 719 670
  | 661 => .call 590 662 .r3
  | 662 => .field .r0 .r1 false 663
  | 663 => .make .r0 (.pair .r0 .r3) 664
  | 664 => .make .r3 .nil 665
  | 665 => .make .r3 (.pair .r0 .r3) 666
  | 666 => .ret .r3
  | 670 => .field .r0 .r0 true 671
  | 671 => .call 660 672 .r3
  | 672 => .field .r2 .r1 true 673
  | 673 => .field .r0 .r2 false 674
  | 674 => .field .r2 .r2 true 675
  | 675 => .make .r2 (.pair .r3 .r2) 676
  | 676 => .field .r1 .r1 false 677
  | 677 => .make .r1 (.pair .r1 .r2) 678
  | 678 => .call 630 679 .r3
  | 679 => .ret .r3
  | 680 => .branch .r0 681 719 719 683
  | 681 => .make .r3 .nil 682
  | 682 => .ret .r3
  | 683 => .field .r2 .r0 false 684
  | 684 => .field .r0 .r0 true 685
  | 685 => .call 680 686 .r3
  | 686 => .make .r2 (.pair .r2 .r3) 687
  | 687 => .field .r0 .r2 false 688
  | 688 => .field .r0 .r0 false 689
  | 689 => .call 580 690 .r3
  | 690 => .branch .r3 691 712 712 719
  | 691 => .field .r0 .r2 false 692
  | 692 => .field .r0 .r0 true 693
  | 693 => .field .r1 .r2 true 694
  | 694 => .branch .r1 710 719 719 695
  | 695 => .call 696 697 .r3
  | 696 => .call 520 531 .r3
  | 697 => .ret .r3
  | 700 => .call 660 701 .r3
  | 701 => .move .r0 .r3 702
  | 702 => .move .r1 .r2 703
  | 703 => .call 680 704 .r3
  | 704 => .ret .r3
  | 710 => .move .r3 .r0 711
  | 711 => .ret .r3
  | 712 => .field .r3 .r2 true 713
  | 713 => .ret .r3
  | 714 => .call 680 719 .r3
  | 716 => .call 660 719 .r3
  | 717 => .call 700 719 .r3
  | 718 => .call 630 719 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 720)) (source : Bits) (pc : Fin 720) : NaturalState 720 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem scan_slots (pc : Fin 532) (h : GraphRelaxationProgram.program pc≠.halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (GraphRelaxationProgram.program pc) := by
  by_cases hp : pc.val=531
  · have he : pc=531 := Fin.ext hp
    subst pc;simp [GraphRelaxationProgram.program] at h
  · simp [program,scanLabel,pc.isLt,hp,show ¬pc.val=579 by omega]
theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,cmpLabel,show ¬pc.val+532=531 by omega,show ¬pc.val+532=579 by omega,
      show ¬pc.val+532<532 by omega,show pc.val+532<580 by omega]

theorem run_append {s u v : NaturalState 720} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem order_eq (u target : Bits) : BinaryComparisonProgram.order u target=.eq ↔ value u=value target := by
  have h := compare_spec u target
  cases hl : (BinaryArithmetic.compare u target).less <;>
    cases he : (BinaryArithmetic.compare u target).equal <;>
    simp [BinaryComparisonProgram.order,BinaryComparisonProgram.choose,hl,he] <;>
    simp [hl,he] at h <;> omega

end DirectedFlowCutGap.GraphDiscoveryProgram
