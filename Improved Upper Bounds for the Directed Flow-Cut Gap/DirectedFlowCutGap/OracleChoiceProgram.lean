import DirectedFlowCutGap.ActualDemandOrigin

/-! Literal postprocessing of the actual selected demand record. It reads the
original occurrence and recovered path, constructs the mask and capacity query,
and retains an actual canonical zero vertex for the two default branches. -/
namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def maskLabel (pc : Fin 160) : Fin 484 := ⟨pc.val,by omega⟩
def capLabel (pc : Fin 244) : Fin 484 := ⟨pc.val+160,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 484) : Instruction C → Instruction 484
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 484) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 484 := fun pc =>
  if h : pc.val<160 then
    callable maskLabel (OracleMask.program ⟨pc.val,h⟩)
  else if h : pc.val<404 then
    callable capLabel (CapacityBottleneck.program ⟨pc.val-160,by omega⟩)
  else match pc.val with
  | 410 => .make .r2 (.pair .r0 .r1) 411
  | 411 => .branch .r0 450 483 483 412
  | 412 => .field .r0 .r0 true 413
  | 413 => .field .r1 .r0 false 414
  | 414 => .field .r1 .r1 false 415
  | 415 => .field .r0 .r0 true 416
  | 416 => .field .r0 .r0 false 417
  | 417 => .make .r1 (.pair .r1 .r0) 418
  | 418 => .field .r0 .r2 true 419
  | 419 => .field .r0 .r0 false 420
  | 420 => .call 150 421 .r3
  | 421 => .field .r1 .r2 true 422
  | 422 => .make .r2 (.pair .r2 .r3) 423
  | 423 => .move .r0 .r3 424
  | 424 => .call 400 425 .r3
  | 425 => .branch .r3 426 483 483 432
  | 426 => .field .r0 .r2 false 427
  | 427 => .field .r0 .r0 true 428
  | 428 => .field .r0 .r0 false 429
  | 429 => .field .r0 .r0 false 430
  | 430 => .field .r1 .r2 true 431
  | 431 => .make .r3 (.pair .r1 .r0) 440
  | 432 => .field .r0 .r3 true 433
  | 433 => .field .r1 .r2 true 434
  | 434 => .make .r3 (.pair .r1 .r0) 440
  | 440 => .ret .r3
  | 450 => .field .r0 .r2 true 451
  | 451 => .field .r0 .r0 false 452
  | 452 => .field .r1 .r0 false 453
  | 453 => .field .r0 .r0 true 454
  | 454 => .call 470 455 .r3
  | 455 => .make .r0 (.flag true) 456
  | 456 => .make .r3 (.pair .r0 .r3) 457
  | 457 => .make .r3 (.pair .r3 .r1) 458
  | 458 => .ret .r3
  | 470 => .branch .r0 471 483 483 473
  | 471 => .make .r3 .nil 472
  | 472 => .ret .r3
  | 473 => .field .r0 .r0 true 474
  | 474 => .call 470 475 .r3
  | 475 => .make .r0 (.flag false) 476
  | 476 => .make .r3 (.pair .r0 .r3) 477
  | 477 => .ret .r3
  | 480 => .call 410 481 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 484)) (source : Bits) (pc : Fin 484) : NaturalState 484 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem mask_slots (pc : Fin 160) (h : OracleMask.program pc≠.halt) :
    program (maskLabel pc)=ReferenceProgramLabels.instruction maskLabel (OracleMask.program pc) := by
  simpa [program,maskLabel,pc.isLt] using callable_eq maskLabel (OracleMask.program pc) h
theorem cap_slots (pc : Fin 244) (h : CapacityBottleneck.program pc≠.halt) :
    program (capLabel pc)=ReferenceProgramLabels.instruction capLabel (CapacityBottleneck.program pc) := by
  simpa [program,capLabel,show ¬pc.val+160<160 by omega,show pc.val+160<404 by omega] using callable_eq capLabel (CapacityBottleneck.program pc) h
theorem cap_halt (pc : Fin 244) (h : CapacityBottleneck.program pc=.halt) :
    program (capLabel pc)=.ret .r3 := by
  simp [program,capLabel,show ¬pc.val+160<160 by omega,show pc.val+160<404 by omega,h,callable]

theorem run_append {s u v : NaturalState 484} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.OracleChoice
