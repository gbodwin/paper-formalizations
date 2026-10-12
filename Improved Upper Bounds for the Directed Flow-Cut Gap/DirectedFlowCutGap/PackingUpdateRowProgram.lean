import DirectedFlowCutGap.ActualPackingEntry
import DirectedFlowCutGap.CanonicalRationalSum

/-! Aligned original capacity/weight/mask traversal. A true entry calls the
actual four-arithmetic update; a false entry retains the original record.
Both branches allocate the output spine in original order. -/
namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def label (pc : Fin 480) : Fin 520 := ⟨pc.val,by omega⟩
def callable : Instruction 480 → Instruction 520
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 520 := fun pc =>
  if h : pc.val<480 then callable (PackingEntry.program ⟨pc.val,h⟩)
  else match pc.val with
  | 480 => .branch .r0 481 519 519 483
  | 481 => .make .r3 .nil 482
  | 482 => .ret .r3
  | 483 => .make .r3 (.pair .r0 .r1) 484
  | 484 => .make .r3 (.pair .r3 .r2) 485
  | 485 => .field .r2 .r2 false 486
  | 486 => .field .r2 .r2 false 487
  | 487 => .branch .r2 519 488 490 519
  | 488 => .field .r0 .r1 false 489
  | 489 => .move .r0 .r0 499
  | 490 => .field .r0 .r0 false 491
  | 491 => .field .r1 .r1 false 492
  | 492 => .field .r2 .r3 true 493
  | 493 => .field .r2 .r2 true 494
  | 494 => .make .r2 (.pair .r2 .r1) 495
  | 495 => .field .r1 .r2 false 496
  | 496 => .field .r2 .r2 true 497
  | 497 => .call 440 499 .r0
  | 499 => .make .r3 (.pair .r0 .r3) 500
  | 500 => .field .r2 .r3 true 501
  | 501 => .field .r2 .r2 true 502
  | 502 => .field .r0 .r2 false 503
  | 503 => .field .r0 .r0 true 504
  | 504 => .field .r1 .r2 true 505
  | 505 => .make .r2 (.pair .r0 .r1) 506
  | 506 => .field .r0 .r3 true 507
  | 507 => .field .r0 .r0 false 508
  | 508 => .field .r1 .r0 true 509
  | 509 => .field .r0 .r0 false 510
  | 510 => .field .r0 .r0 true 511
  | 511 => .field .r1 .r1 true 512
  | 512 => .call 480 513 .r0
  | 513 => .field .r1 .r3 false 514
  | 514 => .make .r3 (.pair .r1 .r0) 515
  | 515 => .ret .r3
  | 518 => .call 480 519 .r0
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 520)) (source : Bits) (pc : Fin 520) : NaturalState 520 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def result (amount : Fraction) : List Fraction → List Fraction → List Bool → List Fraction
  | ci::cs,y::ys,f::fs => (if f then PackingEntry.result ci amount y else y)::result amount cs ys fs
  | _,_,_ => []

def steps (amount : Fraction) : List Fraction → List Fraction → List Bool → ℕ
  | ci::cs,y::ys,f::fs => steps amount cs ys fs+(if f then PackingEntry.steps ci amount y+32 else 25)
  | _,_,_ => 3

def cells (amount : Fraction) : List Fraction → List Fraction → List Bool → ℕ
  | ci::cs,y::ys,f::fs => cells amount cs ys fs+(if f then PackingEntry.cells ci amount y+6 else 5)
  | _,_,_ => 1

theorem slots (pc : Fin 480) (h : PackingEntry.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (PackingEntry.program pc) := by
  have he : callable (PackingEntry.program pc)=ReferenceProgramLabels.instruction label (PackingEntry.program pc) := by
    cases hh : PackingEntry.program pc <;> simp_all [callable]
  simpa [program,label,pc.isLt] using he

theorem run_append {s u v : NaturalState 520} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)
end DirectedFlowCutGap.PackingUpdateRow
