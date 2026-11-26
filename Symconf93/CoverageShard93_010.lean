module
public import Symconf93.CoverageShard93_009

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0550 : NodeCoverage93 [40,10,3] 3 40 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0551 : NodeCoverage93 [40,10] 10 43 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0544
    (ChildrenCoverage93.cons _ _ compact93_node_0545
    (ChildrenCoverage93.cons _ _ compact93_node_0546
    (ChildrenCoverage93.cons _ _ compact93_node_0547
    (ChildrenCoverage93.cons _ _ compact93_node_0548
    (ChildrenCoverage93.cons _ _ compact93_node_0549
    (ChildrenCoverage93.cons _ _ compact93_node_0550
    ChildrenCoverage93.nil)))))))

theorem compact93_node_0552 : NodeCoverage93 [40,9] 9 44 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0553 : NodeCoverage93 [40,8] 8 45 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0554 : NodeCoverage93 [40,7] 7 46 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0555 : NodeCoverage93 [40,6] 6 47 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0556 : NodeCoverage93 [40,5] 5 48 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0557 : NodeCoverage93 [40,3] 3 50 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0558 : NodeCoverage93 [40] 40 53 :=
  node_fork93 (B := [40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0483
    (ChildrenCoverage93.cons _ _ compact93_node_0484
    (ChildrenCoverage93.cons _ _ compact93_node_0485
    (ChildrenCoverage93.cons _ _ compact93_node_0486
    (ChildrenCoverage93.cons _ _ compact93_node_0487
    (ChildrenCoverage93.cons _ _ compact93_node_0488
    (ChildrenCoverage93.cons _ _ compact93_node_0489
    (ChildrenCoverage93.cons _ _ compact93_node_0490
    (ChildrenCoverage93.cons _ _ compact93_node_0491
    (ChildrenCoverage93.cons _ _ compact93_node_0492
    (ChildrenCoverage93.cons _ _ compact93_node_0493
    (ChildrenCoverage93.cons _ _ compact93_node_0494
    (ChildrenCoverage93.cons _ _ compact93_node_0495
    (ChildrenCoverage93.cons _ _ compact93_node_0496
    (ChildrenCoverage93.cons _ _ compact93_node_0497
    (ChildrenCoverage93.cons _ _ compact93_node_0498
    (ChildrenCoverage93.cons _ _ compact93_node_0499
    (ChildrenCoverage93.cons _ _ compact93_node_0500
    (ChildrenCoverage93.cons _ _ compact93_node_0501
    (ChildrenCoverage93.cons _ _ compact93_node_0502
    (ChildrenCoverage93.cons _ _ compact93_node_0520
    (ChildrenCoverage93.cons _ _ compact93_node_0521
    (ChildrenCoverage93.cons _ _ compact93_node_0522
    (ChildrenCoverage93.cons _ _ compact93_node_0523
    (ChildrenCoverage93.cons _ _ compact93_node_0524
    (ChildrenCoverage93.cons _ _ compact93_node_0525
    (ChildrenCoverage93.cons _ _ compact93_node_0526
    (ChildrenCoverage93.cons _ _ compact93_node_0527
    (ChildrenCoverage93.cons _ _ compact93_node_0528
    (ChildrenCoverage93.cons _ _ compact93_node_0529
    (ChildrenCoverage93.cons _ _ compact93_node_0551
    (ChildrenCoverage93.cons _ _ compact93_node_0552
    (ChildrenCoverage93.cons _ _ compact93_node_0553
    (ChildrenCoverage93.cons _ _ compact93_node_0554
    (ChildrenCoverage93.cons _ _ compact93_node_0555
    (ChildrenCoverage93.cons _ _ compact93_node_0556
    (ChildrenCoverage93.cons _ _ compact93_node_0557
    ChildrenCoverage93.nil)))))))))))))))))))))))))))))))))))))

theorem compact93_node_0559 : NodeCoverage93 [39] 39 54 :=
  demand_node_prune93 39 compact93_demands_39 compact93_demands_39_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0560 : NodeCoverage93 [38] 38 55 :=
  demand_node_prune93 38 compact93_demands_38 compact93_demands_38_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0561 : NodeCoverage93 [37] 37 56 :=
  demand_node_prune93 37 compact93_demands_37 compact93_demands_37_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0562 : NodeCoverage93 [36,36,21] 21 0 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0563 : NodeCoverage93 [36,36,18,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0564 : NodeCoverage93 [36,36,18] 18 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0563
    ChildrenCoverage93.nil)

theorem compact93_node_0565 : NodeCoverage93 [36,36,17] 17 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0566 : NodeCoverage93 [36,36,16] 16 5 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0567 : NodeCoverage93 [36,36,15] 15 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0568 : NodeCoverage93 [36,36,14] 14 7 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0569 : NodeCoverage93 [36,36,13] 13 8 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0570 : NodeCoverage93 [36,36,12,9] 9 0 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0571 : NodeCoverage93 [36,36,12,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0572 : NodeCoverage93 [36,36,12,5] 5 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0573 : NodeCoverage93 [36,36,12,3] 3 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0574 : NodeCoverage93 [36,36,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0570
    (ChildrenCoverage93.cons _ _ compact93_node_0571
    (ChildrenCoverage93.cons _ _ compact93_node_0572
    (ChildrenCoverage93.cons _ _ compact93_node_0573
    ChildrenCoverage93.nil))))

theorem compact93_node_0575 : NodeCoverage93 [36,36,11] 11 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0576 : NodeCoverage93 [36,36,10] 10 11 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0577 : NodeCoverage93 [36,36,9] 9 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0578 : NodeCoverage93 [36,36,8] 8 13 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0579 : NodeCoverage93 [36,36,7] 7 14 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0580 : NodeCoverage93 [36,36,6,6,6,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0581 : NodeCoverage93 [36,36,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0580
    ChildrenCoverage93.nil)

theorem compact93_node_0582 : NodeCoverage93 [36,36,6,6,5] 5 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0583 : NodeCoverage93 [36,36,6,6,3] 3 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0584 : NodeCoverage93 [36,36,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0581
    (ChildrenCoverage93.cons _ _ compact93_node_0582
    (ChildrenCoverage93.cons _ _ compact93_node_0583
    ChildrenCoverage93.nil)))

theorem compact93_node_0585 : NodeCoverage93 [36,36,6,5] 5 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0586 : NodeCoverage93 [36,36,6,3] 3 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0587 : NodeCoverage93 [36,36,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0584
    (ChildrenCoverage93.cons _ _ compact93_node_0585
    (ChildrenCoverage93.cons _ _ compact93_node_0586
    ChildrenCoverage93.nil)))

theorem compact93_node_0588 : NodeCoverage93 [36,36,5] 5 16 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0589 : NodeCoverage93 [36,36,3] 3 18 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0590 : NodeCoverage93 [36,36] 36 21 :=
  node_fork93 (B := [21,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0562
    (ChildrenCoverage93.cons _ _ compact93_node_0564
    (ChildrenCoverage93.cons _ _ compact93_node_0565
    (ChildrenCoverage93.cons _ _ compact93_node_0566
    (ChildrenCoverage93.cons _ _ compact93_node_0567
    (ChildrenCoverage93.cons _ _ compact93_node_0568
    (ChildrenCoverage93.cons _ _ compact93_node_0569
    (ChildrenCoverage93.cons _ _ compact93_node_0574
    (ChildrenCoverage93.cons _ _ compact93_node_0575
    (ChildrenCoverage93.cons _ _ compact93_node_0576
    (ChildrenCoverage93.cons _ _ compact93_node_0577
    (ChildrenCoverage93.cons _ _ compact93_node_0578
    (ChildrenCoverage93.cons _ _ compact93_node_0579
    (ChildrenCoverage93.cons _ _ compact93_node_0587
    (ChildrenCoverage93.cons _ _ compact93_node_0588
    (ChildrenCoverage93.cons _ _ compact93_node_0589
    ChildrenCoverage93.nil))))))))))))))))

theorem compact93_node_0591 : NodeCoverage93 [36,35] 35 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0592 : NodeCoverage93 [36,34] 34 23 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0593 : NodeCoverage93 [36,33] 33 24 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0594 : NodeCoverage93 [36,32] 32 25 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0595 : NodeCoverage93 [36,31] 31 26 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0596 : NodeCoverage93 [36,30] 30 27 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0597 : NodeCoverage93 [36,29] 29 28 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0598 : NodeCoverage93 [36,28] 28 29 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0599 : NodeCoverage93 [36,27] 27 30 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0600 : NodeCoverage93 [36,26] 26 31 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0601 : NodeCoverage93 [36,25] 25 32 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0602 : NodeCoverage93 [36,24] 24 33 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0603 : NodeCoverage93 [36,23] 23 34 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
