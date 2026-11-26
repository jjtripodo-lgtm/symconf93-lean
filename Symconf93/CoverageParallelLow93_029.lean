module
public import Symconf93.CoverageParallelLow93_028

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3504 : NodeCoverage93 [12,6,6,6,6,6,3] 3 48 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3505 : NodeCoverage93 [12,6,6,6,6,6] 6 51 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3502
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3503
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3504
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3506 : NodeCoverage93 [12,6,6,6,6,5] 5 52 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3507 : NodeCoverage93 [12,6,6,6,6,3] 3 54 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3508 : NodeCoverage93 [12,6,6,6,6] 6 57 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3505
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3506
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3507
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3509 : NodeCoverage93 [12,6,6,6,5] 5 58 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3510 : NodeCoverage93 [12,6,6,6,3] 3 60 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3511 : NodeCoverage93 [12,6,6,6] 6 63 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3508
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3509
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3510
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3512 : NodeCoverage93 [12,6,6,5] 5 64 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3513 : NodeCoverage93 [12,6,6,3] 3 66 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3514 : NodeCoverage93 [12,6,6] 6 69 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3511
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3512
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3513
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3515 : NodeCoverage93 [12,6,5] 5 70 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3516 : NodeCoverage93 [12,6,3] 3 72 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3517 : NodeCoverage93 [12,6] 6 75 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3514
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3515
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3516
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3518 : NodeCoverage93 [12,5] 5 76 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3519 : NodeCoverage93 [12,3] 3 78 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3520 : NodeCoverage93 [12] 12 81 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3394
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3411
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3426
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3445
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3446
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3459
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3517
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3518
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3519
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_3521 : NodeCoverage93 [11,11,11,11,11,11,11,11,5] 5 0 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3522 : NodeCoverage93 [11,11,11,11,11,11,11,11] 11 5 :=
  node_fork93 (B := [5]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3521
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3523 : NodeCoverage93 [11,11,11,11,11,11,11,10] 10 6 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3524 : NodeCoverage93 [11,11,11,11,11,11,11,9] 9 7 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3525 : NodeCoverage93 [11,11,11,11,11,11,11,8] 8 8 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3526 : NodeCoverage93 [11,11,11,11,11,11,11,7] 7 9 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3527 : NodeCoverage93 [11,11,11,11,11,11,11,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3528 : NodeCoverage93 [11,11,11,11,11,11,11,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3529 : NodeCoverage93 [11,11,11,11,11,11,11,3] 3 13 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3530 : NodeCoverage93 [11,11,11,11,11,11,11] 11 16 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3522
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3523
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3524
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3525
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3526
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3527
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3528
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3529
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3531 : NodeCoverage93 [11,11,11,11,11,11,10] 10 17 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3532 : NodeCoverage93 [11,11,11,11,11,11,9] 9 18 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3533 : NodeCoverage93 [11,11,11,11,11,11,8] 8 19 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3534 : NodeCoverage93 [11,11,11,11,11,11,7] 7 20 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3535 : NodeCoverage93 [11,11,11,11,11,11,6] 6 21 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3536 : NodeCoverage93 [11,11,11,11,11,11,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3537 : NodeCoverage93 [11,11,11,11,11,11,3] 3 24 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3538 : NodeCoverage93 [11,11,11,11,11,11] 11 27 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3530
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3531
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3532
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3533
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3534
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3535
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3536
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3537
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3539 : NodeCoverage93 [11,11,11,11,11,10] 10 28 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3540 : NodeCoverage93 [11,11,11,11,11,9] 9 29 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3541 : NodeCoverage93 [11,11,11,11,11,8] 8 30 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3542 : NodeCoverage93 [11,11,11,11,11,7] 7 31 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3543 : NodeCoverage93 [11,11,11,11,11,6] 6 32 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3544 : NodeCoverage93 [11,11,11,11,11,5] 5 33 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3545 : NodeCoverage93 [11,11,11,11,11,3] 3 35 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3546 : NodeCoverage93 [11,11,11,11,11] 11 38 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3538
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3539
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3540
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3541
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3542
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3543
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3544
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3545
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3547 : NodeCoverage93 [11,11,11,11,10] 10 39 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3548 : NodeCoverage93 [11,11,11,11,9] 9 40 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3549 : NodeCoverage93 [11,11,11,11,8] 8 41 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3550 : NodeCoverage93 [11,11,11,11,7] 7 42 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3551 : NodeCoverage93 [11,11,11,11,6] 6 43 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3552 : NodeCoverage93 [11,11,11,11,5] 5 44 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3553 : NodeCoverage93 [11,11,11,11,3] 3 46 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3554 : NodeCoverage93 [11,11,11,11] 11 49 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3546
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3547
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3548
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3549
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3550
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3551
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3552
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3553
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3555 : NodeCoverage93 [11,11,11,10] 10 50 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3556 : NodeCoverage93 [11,11,11,9] 9 51 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3557 : NodeCoverage93 [11,11,11,8] 8 52 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3558 : NodeCoverage93 [11,11,11,7] 7 53 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3559 : NodeCoverage93 [11,11,11,6] 6 54 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3560 : NodeCoverage93 [11,11,11,5] 5 55 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3561 : NodeCoverage93 [11,11,11,3] 3 57 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3562 : NodeCoverage93 [11,11,11] 11 60 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3554
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3555
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3556
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3557
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3558
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3559
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3560
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3561
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3563 : NodeCoverage93 [11,11,10] 10 61 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3564 : NodeCoverage93 [11,11,9] 9 62 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3565 : NodeCoverage93 [11,11,8] 8 63 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3566 : NodeCoverage93 [11,11,7] 7 64 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
