import DirectedFlowCutGap.GraphAdjacencyProgram
import DirectedFlowCutGap.GraphWalkExtension

/-! The fixed table for a genuine tail-first graph relaxation scan. Each true
adjacency branch constructs its edge and cost; stable ties choose that head. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

abbrev Entry := Bits×Walk

def StoredEntry (heap : NaturalHeap) (p : ℕ) (x : Entry) : Prop :=
  ∃ vertex walk,heap[p]?=some (.pair vertex walk) ∧ BoolList heap vertex x.1 ∧ StoredWalk heap walk x.2
inductive Table (heap : NaturalHeap) : ℕ → List Entry → Prop
  | nil {p} : heap[p]?=some .nil → Table heap p []
  | cons {p head tail x xs} : heap[p]?=some (.pair head tail) → StoredEntry heap head x →
      Table heap tail xs → Table heap p (x::xs)
def StoredOption (heap : NaturalHeap) (p : ℕ) : Option Walk → Prop
  | none => heap[p]?=some .nil
  | some q => StoredWalk heap p q

def Context (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits) (rows : List Fraction)
    (u sw : Bits) : Prop :=
  ∃ ur mix matrix cost,heap[p]?=some (.pair ur mix) ∧ heap[mix]?=some (.pair matrix cost) ∧
    BoolList heap ur u ∧ GraphAdjacencyProgram.Matrix heap matrix adjacency ∧
    OutgoingCostProgram.Context heap cost rows sw

theorem entry_extend {heap : NaturalHeap} {p : ℕ} {x : Entry}
    (h : StoredEntry heap p x) (extra : NaturalHeap) : StoredEntry (heap++extra) p x := by
  obtain ⟨v,q,hp,hv,hq⟩ := h
  exact ⟨v,q,lookup_extend hp extra,boolList_extend hv extra,walk_extend hq extra⟩
theorem table_extend {heap : NaturalHeap} {p : ℕ} {xs : List Entry}
    (h : Table heap p xs) (extra : NaturalHeap) : Table (heap++extra) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp extra)
  | cons hp hx _ ih => exact .cons (lookup_extend hp extra) (entry_extend hx extra) ih

theorem option_extend {heap : NaturalHeap} {p : ℕ} {q : Option Walk}
    (h : StoredOption heap p q) (extra : NaturalHeap) : StoredOption (heap++extra) p q := by
  cases q with
  | none => exact lookup_extend h extra
  | some q => exact walk_extend h extra

theorem context_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits} {rows : List Fraction} {u sw : Bits}
    (h : Context heap p adjacency rows u sw) (extra : NaturalHeap) : Context (heap++extra) p adjacency rows u sw := by
  obtain ⟨ur,mix,matrix,cost,hp,hm,hu,ha,hc⟩ := h
  exact ⟨ur,mix,matrix,cost,lookup_extend hp extra,lookup_extend hm extra,boolList_extend hu extra,
    GraphAdjacencyProgram.matrix_extend ha extra,PathCostMaterialization.context_extend hc extra⟩

def adjacent (adjacency : List Bits) (u v : Bits) : Bool := ((adjacency[value u]?).getD [])[value v]?.getD false

def choose (x y : Walk) : Walk := if (BinaryRational.le x.cost y.cost).1 then x else y

def pick (x : Walk) : Option Walk → Option Walk
  | none => some x
  | some y => some (choose x y)

def scan (adjacency : List Bits) (rows : List Fraction) (sw u : Bits) : List Entry → Option Walk
  | [] => none
  | x::xs =>
    let tail := scan adjacency rows sw u xs
    if adjacent adjacency u x.1 then pick (GraphWalkExtension.result rows sw (u,x.1) x.2) tail else tail

def testSteps (u v : Bits) : ℕ := GraphAdjacencyProgram.steps u v+10
def testCells (u v : Bits) : ℕ := value u+value v+3
def extendSteps (rows : List Fraction) (sw : Bits) (e : Bits×Bits) (q : Walk) : ℕ :=
  GraphWalkExtension.steps rows sw e q+7
def pickSteps (x y : Walk) : ℕ := RationalComparisonProgram.instructions x.cost y.cost+8
def pickCells (x y : Walk) : ℕ := RationalComparisonProgram.cells x.cost y.cost+1

def steps (adjacency : List Bits) (rows : List Fraction) (sw u : Bits) : List Entry → ℕ
  | [] => 3
  | x::xs => steps adjacency rows sw u xs+testSteps u x.1+
      if adjacent adjacency u x.1 then extendSteps rows sw (u,x.1) x.2+
        (match scan adjacency rows sw u xs with
        | none => 18
        | some y => 20+pickSteps (GraphWalkExtension.result rows sw (u,x.1) x.2) y)
      else 10

def cells (adjacency : List Bits) (rows : List Fraction) (sw u : Bits) : List Entry → ℕ
  | [] => 1
  | x::xs => cells adjacency rows sw u xs+1+testCells u x.1+
      if adjacent adjacency u x.1 then 1+GraphWalkExtension.cells rows sw (u,x.1) x.2+
        (match scan adjacency rows sw u xs with
        | none => 0
        | some y => pickCells (GraphWalkExtension.result rows sw (u,x.1) x.2) y)
      else 0

def adjLabel (pc : Fin 36) : Fin 532 := ⟨pc.val,by omega⟩
def extLabel (pc : Fin 270) : Fin 532 := ⟨pc.val+36,by omega⟩
def cmpLabel (pc : Fin 158) : Fin 532 := ⟨pc.val+306,by omega⟩
def program : Program 532 := fun pc =>
  if pc.val=35 then .ret .r3
  else if pc.val=305 then .ret .r3
  else if pc.val=463 then .ret .r3
  else if h : pc.val<36 then
    ReferenceProgramLabels.instruction adjLabel (GraphAdjacencyProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<306 then
    ReferenceProgramLabels.instruction extLabel (GraphWalkExtension.program ⟨pc.val-36,by omega⟩)
  else if h : pc.val<464 then
    ReferenceProgramLabels.instruction cmpLabel (RationalComparisonProgram.program ⟨pc.val-306,by omega⟩)
  else match pc.val with
  | 464 => .branch .r0 465 531 531 467
  | 465 => .make .r3 .nil 466
  | 466 => .ret .r3
  | 467 => .field .r2 .r0 false 468
  | 468 => .field .r0 .r0 true 469
  | 469 => .call 464 470 .r3
  | 470 => .make .r2 (.pair .r2 .r3) 471
  | 471 => .field .r0 .r2 false 472
  | 472 => .call 500 473 .r3
  | 473 => .branch .r3 531 495 474 531
  | 474 => .field .r0 .r1 false 475
  | 475 => .field .r3 .r2 false 476
  | 476 => .field .r3 .r3 false 477
  | 477 => .make .r0 (.pair .r0 .r3) 478
  | 478 => .field .r3 .r2 false 479
  | 479 => .field .r3 .r3 true 480
  | 480 => .call 510 481 .r3
  | 481 => .field .r1 .r2 true 482
  | 482 => .branch .r1 493 531 531 483
  | 483 => .move .r0 .r3 484
  | 484 => .call 520 485 .r3
  | 485 => .ret .r3
  | 493 => .ret .r3
  | 495 => .field .r3 .r2 true 496
  | 496 => .ret .r3
  | 500 => .field .r0 .r0 false 501
  | 501 => .field .r2 .r1 true 502
  | 502 => .field .r2 .r2 false 503
  | 503 => .make .r2 (.pair .r2 .r0) 504
  | 504 => .field .r0 .r1 false 505
  | 505 => .move .r1 .r2 506
  | 506 => .call 34 507 .r3
  | 507 => .ret .r3
  | 510 => .field .r2 .r1 true 511
  | 511 => .field .r2 .r2 true 512
  | 512 => .move .r1 .r3 513
  | 513 => .call 304 514 .r3
  | 514 => .ret .r3
  | 520 => .make .r2 (.pair .r0 .r1) 521
  | 521 => .field .r0 .r0 true 522
  | 522 => .field .r1 .r1 true 523
  | 523 => .call 450 524 .r3
  | 524 => .branch .r3 531 526 525 531
  | 525 => .field .r3 .r2 false 527
  | 526 => .field .r3 .r2 true 527
  | 527 => .ret .r3
  | 530 => .call 464 531 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 532)) (source : Bits) (pc : Fin 532) : NaturalState 532 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem adj_slots (pc : Fin 36) (h : GraphAdjacencyProgram.program pc≠.halt) :
    program (adjLabel pc)=ReferenceProgramLabels.instruction adjLabel (GraphAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=35
  · have he : pc=35 := Fin.ext hp
    subst pc;simp [GraphAdjacencyProgram.program] at h
  · simp [program,adjLabel,pc.isLt,hp,show ¬pc.val=305 by omega,show ¬pc.val=463 by omega]
theorem ext_slots (pc : Fin 270) (h : GraphWalkExtension.program pc≠.halt) :
    program (extLabel pc)=ReferenceProgramLabels.instruction extLabel (GraphWalkExtension.program pc) := by
  by_cases hp : pc.val=269
  · have he : pc=269 := Fin.ext hp
    subst pc;simp [GraphWalkExtension.program] at h
  · simp [program,extLabel,show ¬pc.val+36=35 by omega,show ¬pc.val+36=305 by omega,
      show ¬pc.val+36=463 by omega,show ¬pc.val+36<36 by omega,show pc.val+36<306 by omega]
theorem cmp_slots (pc : Fin 158) (h : RationalComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (RationalComparisonProgram.program pc) := by
  by_cases hp : pc.val=157
  · have he : pc=157 := Fin.ext hp
    subst pc;simp [RationalComparisonProgram.program] at h
  · simp [program,cmpLabel,show ¬pc.val+306=35 by omega,show ¬pc.val+306=305 by omega,
      show ¬pc.val+306=463 by omega,show ¬pc.val+306<36 by omega,show ¬pc.val+306<306 by omega,
      show pc.val+306<464 by omega]

theorem run_append {s u v : NaturalState 532} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.GraphRelaxationProgram
