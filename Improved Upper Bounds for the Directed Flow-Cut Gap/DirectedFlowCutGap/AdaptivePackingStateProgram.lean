import DirectedFlowCutGap.ActualPackingGuard
import DirectedFlowCutGap.ActualPackingUpdateRow
import DirectedFlowCutGap.ActualPackingLoadRow
import DirectedFlowCutGap.ActualPackingAmount
import DirectedFlowCutGap.ActualPackingStart

/-! A finite adaptive controller. Its guard, oracle, bottleneck read,
normalization, best comparison, weight/total/load updates and state allocation
all run on actual same-heap records. The universal composition proof is separate. -/
namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def guardLabel (pc : Fin 484) : Fin 4800 := ⟨pc.val+0,by omega⟩

def contextLabel (pc : Fin 10) : Fin 4800 := ⟨pc.val+484,by omega⟩

def oracleLabel (pc : Fin 2120) : Fin 4800 := ⟨pc.val+494,by omega⟩

def amountLabel (pc : Fin 44) : Fin 4800 := ⟨pc.val+2614,by omega⟩

def normalizedLabel (pc : Fin 372) : Fin 4800 := ⟨pc.val+2658,by omega⟩

def objectiveLabel (pc : Fin 312) : Fin 4800 := ⟨pc.val+3030,by omega⟩

def comparisonLabel (pc : Fin 158) : Fin 4800 := ⟨pc.val+3342,by omega⟩

def weightsLabel (pc : Fin 520) : Fin 4800 := ⟨pc.val+3500,by omega⟩

def additionLabel (pc : Fin 142) : Fin 4800 := ⟨pc.val+4020,by omega⟩

def loadsLabel (pc : Fin 200) : Fin 4800 := ⟨pc.val+4162,by omega⟩

def callable {C : ℕ} (label : Fin C → Fin 4800) (result : Reg) : Instruction C → Instruction 4800
  | .halt => .ret result
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 4800) (result : Reg)
    (op : Instruction C) (h : op≠.halt) :
    callable label result op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 4800 := fun pc =>
  if h : pc.val<484 then callable guardLabel .r3 (PackingGuard.program ⟨pc.val-0,by omega⟩)
  else if h : pc.val<494 then callable contextLabel .r3 (PackingGraphContext.program ⟨pc.val-484,by omega⟩)
  else if h : pc.val<2614 then callable oracleLabel .r3 (GraphOracleMachine.program ⟨pc.val-494,by omega⟩)
  else if h : pc.val<2658 then callable amountLabel .r3 (PackingAmount.program ⟨pc.val-2614,by omega⟩)
  else if h : pc.val<3030 then callable normalizedLabel .r3 (NormalizedRow.program ⟨pc.val-2658,by omega⟩)
  else if h : pc.val<3342 then callable objectiveLabel .r3 (ObjectiveRow.program ⟨pc.val-3030,by omega⟩)
  else if h : pc.val<3500 then callable comparisonLabel .r3 (RationalComparisonProgram.program ⟨pc.val-3342,by omega⟩)
  else if h : pc.val<4020 then callable weightsLabel .r0 (PackingUpdateRow.program ⟨pc.val-3500,by omega⟩)
  else if h : pc.val<4162 then callable additionLabel .r3 (CanonicalRationalAddition.program ⟨pc.val-4020,by omega⟩)
  else if h : pc.val<4362 then callable loadsLabel .r0 (PackingLoadRow.program ⟨pc.val-4162,by omega⟩)
  else match pc.val with
  | 4400 => .call 470 4401 .r3
  | 4401 => .branch .r3 4799 4402 4798 4799
  | 4402 => .make .r2 (.pair .r1 .r2) 4403
  | 4403 => .make .r2 (.pair .r0 .r2) 4404
  | 4404 => .field .r0 .r2 true 4405
  | 4405 => .field .r0 .r0 false 4406
  | 4406 => .field .r0 .r0 false 4407
  | 4407 => .field .r1 .r2 true 4408
  | 4408 => .field .r1 .r1 true 4409
  | 4409 => .field .r1 .r1 true 4410
  | 4410 => .call 492 4411 .r3
  | 4411 => .move .r1 .r3 4412
  | 4412 => .field .r0 .r2 true 4413
  | 4413 => .field .r0 .r0 true 4414
  | 4414 => .field .r0 .r0 false 4415
  | 4415 => .call 2594 4416 .r3
  | 4416 => .make .r2 (.pair .r3 .r2) 4417
  | 4417 => .field .r0 .r2 false 4418
  | 4418 => .field .r1 .r2 true 4419
  | 4419 => .field .r1 .r1 false 4420
  | 4420 => .call 2654 4421 .r3
  | 4421 => .make .r2 (.pair .r3 .r2) 4422
  | 4422 => .field .r0 .r2 true 4423
  | 4423 => .field .r0 .r0 true 4424
  | 4424 => .field .r0 .r0 true 4425
  | 4425 => .field .r0 .r0 false 4426
  | 4426 => .field .r0 .r0 false 4427
  | 4427 => .field .r1 .r2 true 4428
  | 4428 => .field .r1 .r1 false 4429
  | 4429 => .field .r1 .r1 false 4430
  | 4430 => .call 3022 4431 .r3
  | 4431 => .make .r2 (.pair .r3 .r2) 4432
  | 4432 => .field .r0 .r2 true 4433
  | 4433 => .field .r0 .r0 true 4434
  | 4434 => .field .r0 .r0 true 4435
  | 4435 => .field .r0 .r0 false 4436
  | 4436 => .move .r1 .r3 4437
  | 4437 => .call 3338 4438 .r3
  | 4438 => .make .r2 (.pair .r3 .r2) 4439
  | 4439 => .field .r0 .r2 true 4440
  | 4440 => .field .r0 .r0 true 4441
  | 4441 => .field .r0 .r0 true 4442
  | 4442 => .field .r0 .r0 true 4443
  | 4443 => .field .r0 .r0 true 4444
  | 4444 => .field .r0 .r0 false 4445
  | 4445 => .field .r0 .r0 true 4446
  | 4446 => .field .r0 .r0 true 4447
  | 4447 => .field .r0 .r0 false 4448
  | 4448 => .move .r1 .r3 4449
  | 4449 => .call 3486 4450 .r3
  | 4450 => .branch .r3 4799 4451 4455 4799
  | 4451 => .field .r0 .r2 true 4452
  | 4452 => .field .r0 .r0 false 4453
  | 4453 => .field .r1 .r2 false 4454
  | 4454 => .move .r0 .r0 4472
  | 4455 => .field .r0 .r2 true 4456
  | 4456 => .field .r0 .r0 true 4457
  | 4457 => .field .r0 .r0 true 4458
  | 4458 => .field .r0 .r0 true 4459
  | 4459 => .field .r0 .r0 true 4460
  | 4460 => .field .r0 .r0 false 4461
  | 4461 => .field .r0 .r0 true 4462
  | 4462 => .field .r0 .r0 false 4463
  | 4463 => .field .r1 .r2 true 4464
  | 4464 => .field .r1 .r1 true 4465
  | 4465 => .field .r1 .r1 true 4466
  | 4466 => .field .r1 .r1 true 4467
  | 4467 => .field .r1 .r1 true 4468
  | 4468 => .field .r1 .r1 false 4469
  | 4469 => .field .r1 .r1 true 4470
  | 4470 => .field .r1 .r1 true 4471
  | 4471 => .field .r1 .r1 false 4472
  | 4472 => .make .r3 (.pair .r0 .r1) 4473
  | 4473 => .make .r2 (.pair .r3 .r2) 4474
  | 4474 => .field .r0 .r2 true 4475
  | 4475 => .field .r0 .r0 true 4476
  | 4476 => .field .r0 .r0 true 4477
  | 4477 => .field .r0 .r0 true 4478
  | 4478 => .field .r0 .r0 false 4479
  | 4479 => .field .r0 .r0 false 4480
  | 4480 => .field .r1 .r2 true 4481
  | 4481 => .field .r1 .r1 true 4482
  | 4482 => .field .r1 .r1 true 4483
  | 4483 => .field .r1 .r1 false 4484
  | 4484 => .move .r3 .r2 4485
  | 4485 => .make .r2 (.pair .r0 .r1) 4486
  | 4486 => .field .r0 .r3 true 4487
  | 4487 => .field .r0 .r0 true 4488
  | 4488 => .field .r0 .r0 true 4489
  | 4489 => .field .r0 .r0 true 4490
  | 4490 => .field .r0 .r0 true 4491
  | 4491 => .field .r0 .r0 false 4492
  | 4492 => .field .r1 .r3 true 4493
  | 4493 => .field .r1 .r1 true 4494
  | 4494 => .field .r1 .r1 true 4495
  | 4495 => .field .r1 .r1 true 4496
  | 4496 => .field .r1 .r1 true 4497
  | 4497 => .field .r1 .r1 true 4498
  | 4498 => .field .r1 .r1 false 4499
  | 4499 => .field .r1 .r1 false 4500
  | 4500 => .call 4018 4501 .r0
  | 4501 => .make .r2 (.pair .r0 .r3) 4502
  | 4502 => .field .r0 .r2 true 4503
  | 4503 => .field .r0 .r0 true 4504
  | 4504 => .field .r0 .r0 true 4505
  | 4505 => .field .r0 .r0 true 4506
  | 4506 => .field .r0 .r0 true 4507
  | 4507 => .field .r0 .r0 true 4508
  | 4508 => .field .r0 .r0 true 4509
  | 4509 => .field .r0 .r0 false 4510
  | 4510 => .field .r0 .r0 true 4511
  | 4511 => .field .r0 .r0 true 4512
  | 4512 => .field .r0 .r0 true 4513
  | 4513 => .field .r0 .r0 false 4514
  | 4514 => .field .r1 .r2 true 4515
  | 4515 => .field .r1 .r1 true 4516
  | 4516 => .field .r1 .r1 true 4517
  | 4517 => .field .r1 .r1 true 4518
  | 4518 => .field .r1 .r1 false 4519
  | 4519 => .call 4160 4520 .r3
  | 4520 => .make .r2 (.pair .r3 .r2) 4521
  | 4521 => .field .r0 .r2 true 4522
  | 4522 => .field .r0 .r0 true 4523
  | 4523 => .field .r0 .r0 true 4524
  | 4524 => .field .r0 .r0 true 4525
  | 4525 => .field .r0 .r0 true 4526
  | 4526 => .field .r0 .r0 true 4527
  | 4527 => .field .r0 .r0 false 4528
  | 4528 => .field .r0 .r0 false 4529
  | 4529 => .field .r1 .r2 true 4530
  | 4530 => .field .r1 .r1 true 4531
  | 4531 => .field .r1 .r1 true 4532
  | 4532 => .field .r1 .r1 true 4533
  | 4533 => .field .r1 .r1 true 4534
  | 4534 => .field .r1 .r1 false 4535
  | 4535 => .make .r1 (.pair .r0 .r1) 4536
  | 4536 => .field .r0 .r2 true 4537
  | 4537 => .field .r0 .r0 true 4538
  | 4538 => .field .r0 .r0 true 4539
  | 4539 => .field .r0 .r0 true 4540
  | 4540 => .field .r0 .r0 true 4541
  | 4541 => .field .r0 .r0 true 4542
  | 4542 => .field .r0 .r0 true 4543
  | 4543 => .field .r0 .r0 true 4544
  | 4544 => .field .r0 .r0 false 4545
  | 4545 => .field .r0 .r0 true 4546
  | 4546 => .field .r0 .r0 true 4547
  | 4547 => .field .r0 .r0 true 4548
  | 4548 => .field .r0 .r0 true 4549
  | 4549 => .field .r0 .r0 false 4550
  | 4550 => .call 4352 4551 .r0
  | 4551 => .make .r2 (.pair .r0 .r2) 4552
  | 4552 => .field .r0 .r2 true 4553
  | 4553 => .field .r0 .r0 true 4554
  | 4554 => .field .r0 .r0 true 4555
  | 4555 => .field .r0 .r0 true 4556
  | 4556 => .field .r0 .r0 true 4557
  | 4557 => .field .r0 .r0 true 4558
  | 4558 => .field .r0 .r0 true 4559
  | 4559 => .field .r0 .r0 false 4560
  | 4560 => .field .r1 .r2 true 4561
  | 4561 => .field .r1 .r1 true 4562
  | 4562 => .field .r1 .r1 true 4563
  | 4563 => .field .r1 .r1 true 4564
  | 4564 => .field .r1 .r1 true 4565
  | 4565 => .field .r1 .r1 true 4566
  | 4566 => .field .r1 .r1 false 4567
  | 4567 => .make .r0 (.pair .r0 .r1) 4568
  | 4568 => .field .r1 .r2 true 4569
  | 4569 => .field .r1 .r1 true 4570
  | 4570 => .field .r1 .r1 true 4571
  | 4571 => .field .r1 .r1 true 4572
  | 4572 => .field .r1 .r1 true 4573
  | 4573 => .field .r1 .r1 true 4574
  | 4574 => .field .r1 .r1 true 4575
  | 4575 => .field .r1 .r1 true 4576
  | 4576 => .field .r1 .r1 true 4577
  | 4577 => .field .r1 .r1 false 4578
  | 4578 => .field .r1 .r1 true 4579
  | 4579 => .field .r1 .r1 true 4580
  | 4580 => .field .r1 .r1 true 4581
  | 4581 => .field .r1 .r1 true 4582
  | 4582 => .field .r1 .r1 true 4583
  | 4583 => .make .r3 (.pair .r0 .r1) 4584
  | 4584 => .field .r0 .r2 false 4585
  | 4585 => .make .r3 (.pair .r0 .r3) 4586
  | 4586 => .field .r0 .r2 true 4587
  | 4587 => .field .r0 .r0 false 4588
  | 4588 => .make .r3 (.pair .r0 .r3) 4589
  | 4589 => .field .r0 .r2 true 4590
  | 4590 => .field .r0 .r0 true 4591
  | 4591 => .field .r0 .r0 true 4592
  | 4592 => .field .r0 .r0 false 4593
  | 4593 => .field .r0 .r0 true 4594
  | 4594 => .make .r3 (.pair .r0 .r3) 4595
  | 4595 => .field .r0 .r2 true 4596
  | 4596 => .field .r0 .r0 true 4597
  | 4597 => .field .r0 .r0 true 4598
  | 4598 => .field .r0 .r0 false 4599
  | 4599 => .field .r0 .r0 false 4600
  | 4600 => .make .r3 (.pair .r0 .r3) 4601
  | 4601 => .field .r0 .r2 true 4602
  | 4602 => .field .r0 .r0 true 4603
  | 4603 => .field .r0 .r0 false 4604
  | 4604 => .make .r3 (.pair .r0 .r3) 4605
  | 4798 => .move .r3 .r1 4799
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 4800)) (source : Bits) (pc : Fin 4800) : NaturalState 4800 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem guard_slots (pc : Fin 484) (h : PackingGuard.program pc≠.halt) :
    program (guardLabel pc)=ReferenceProgramLabels.instruction guardLabel (PackingGuard.program pc) := by
  simpa [program,guardLabel,show pc.val+0<484 by omega] using callable_eq guardLabel .r3 (PackingGuard.program pc) h

theorem context_slots (pc : Fin 10) (h : PackingGraphContext.program pc≠.halt) :
    program (contextLabel pc)=ReferenceProgramLabels.instruction contextLabel (PackingGraphContext.program pc) := by
  simpa [program,contextLabel,show ¬pc.val+484<484 by omega,show pc.val+484<494 by omega] using callable_eq contextLabel .r3 (PackingGraphContext.program pc) h

theorem oracle_slots (pc : Fin 2120) (h : GraphOracleMachine.program pc≠.halt) :
    program (oracleLabel pc)=ReferenceProgramLabels.instruction oracleLabel (GraphOracleMachine.program pc) := by
  simpa [program,oracleLabel,show ¬pc.val+494<484 by omega,show ¬pc.val+494<494 by omega,show pc.val+494<2614 by omega] using callable_eq oracleLabel .r3 (GraphOracleMachine.program pc) h

theorem amount_slots (pc : Fin 44) (h : PackingAmount.program pc≠.halt) :
    program (amountLabel pc)=ReferenceProgramLabels.instruction amountLabel (PackingAmount.program pc) := by
  simpa [program,amountLabel,show ¬pc.val+2614<484 by omega,show ¬pc.val+2614<494 by omega,show ¬pc.val+2614<2614 by omega,show pc.val+2614<2658 by omega] using callable_eq amountLabel .r3 (PackingAmount.program pc) h

theorem normalized_slots (pc : Fin 372) (h : NormalizedRow.program pc≠.halt) :
    program (normalizedLabel pc)=ReferenceProgramLabels.instruction normalizedLabel (NormalizedRow.program pc) := by
  simpa [program,normalizedLabel,show ¬pc.val+2658<484 by omega,show ¬pc.val+2658<494 by omega,show ¬pc.val+2658<2614 by omega,show ¬pc.val+2658<2658 by omega,show pc.val+2658<3030 by omega] using callable_eq normalizedLabel .r3 (NormalizedRow.program pc) h

theorem objective_slots (pc : Fin 312) (h : ObjectiveRow.program pc≠.halt) :
    program (objectiveLabel pc)=ReferenceProgramLabels.instruction objectiveLabel (ObjectiveRow.program pc) := by
  simpa [program,objectiveLabel,show ¬pc.val+3030<484 by omega,show ¬pc.val+3030<494 by omega,show ¬pc.val+3030<2614 by omega,show ¬pc.val+3030<2658 by omega,show ¬pc.val+3030<3030 by omega,show pc.val+3030<3342 by omega] using callable_eq objectiveLabel .r3 (ObjectiveRow.program pc) h

theorem comparison_slots (pc : Fin 158) (h : RationalComparisonProgram.program pc≠.halt) :
    program (comparisonLabel pc)=ReferenceProgramLabels.instruction comparisonLabel (RationalComparisonProgram.program pc) := by
  simpa [program,comparisonLabel,show ¬pc.val+3342<484 by omega,show ¬pc.val+3342<494 by omega,show ¬pc.val+3342<2614 by omega,show ¬pc.val+3342<2658 by omega,show ¬pc.val+3342<3030 by omega,show ¬pc.val+3342<3342 by omega,show pc.val+3342<3500 by omega] using callable_eq comparisonLabel .r3 (RationalComparisonProgram.program pc) h

theorem weights_slots (pc : Fin 520) (h : PackingUpdateRow.program pc≠.halt) :
    program (weightsLabel pc)=ReferenceProgramLabels.instruction weightsLabel (PackingUpdateRow.program pc) := by
  simpa [program,weightsLabel,show ¬pc.val+3500<484 by omega,show ¬pc.val+3500<494 by omega,show ¬pc.val+3500<2614 by omega,show ¬pc.val+3500<2658 by omega,show ¬pc.val+3500<3030 by omega,show ¬pc.val+3500<3342 by omega,show ¬pc.val+3500<3500 by omega,show pc.val+3500<4020 by omega] using callable_eq weightsLabel .r0 (PackingUpdateRow.program pc) h

theorem addition_slots (pc : Fin 142) (h : CanonicalRationalAddition.program pc≠.halt) :
    program (additionLabel pc)=ReferenceProgramLabels.instruction additionLabel (CanonicalRationalAddition.program pc) := by
  simpa [program,additionLabel,show ¬pc.val+4020<484 by omega,show ¬pc.val+4020<494 by omega,show ¬pc.val+4020<2614 by omega,show ¬pc.val+4020<2658 by omega,show ¬pc.val+4020<3030 by omega,show ¬pc.val+4020<3342 by omega,show ¬pc.val+4020<3500 by omega,show ¬pc.val+4020<4020 by omega,show pc.val+4020<4162 by omega] using callable_eq additionLabel .r3 (CanonicalRationalAddition.program pc) h

theorem loads_slots (pc : Fin 200) (h : PackingLoadRow.program pc≠.halt) :
    program (loadsLabel pc)=ReferenceProgramLabels.instruction loadsLabel (PackingLoadRow.program pc) := by
  simpa [program,loadsLabel,show ¬pc.val+4162<484 by omega,show ¬pc.val+4162<494 by omega,show ¬pc.val+4162<2614 by omega,show ¬pc.val+4162<2658 by omega,show ¬pc.val+4162<3030 by omega,show ¬pc.val+4162<3342 by omega,show ¬pc.val+4162<3500 by omega,show ¬pc.val+4162<4020 by omega,show ¬pc.val+4162<4162 by omega,show pc.val+4162<4362 by omega] using callable_eq loadsLabel .r0 (PackingLoadRow.program pc) h
end DirectedFlowCutGap.AdaptivePackingState
