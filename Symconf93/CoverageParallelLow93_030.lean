module
public import Symconf93.CoverageParallelLow93_029

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3567 : NodeCoverage93 [11,11,6] 6 65 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3568 : NodeCoverage93 [11,11,5] 5 66 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3569 : NodeCoverage93 [11,11,3] 3 68 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3570 : NodeCoverage93 [11,11] 11 71 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3562
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3563
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3564
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3565
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3566
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3567
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3568
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3569
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3571 : NodeCoverage93 [11,10] 10 72 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3572 : NodeCoverage93 [11,9] 9 73 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3573 : NodeCoverage93 [11,8] 8 74 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3574 : NodeCoverage93 [11,7] 7 75 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3575 : NodeCoverage93 [11,6] 6 76 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3576 : NodeCoverage93 [11,5] 5 77 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3577 : NodeCoverage93 [11,3] 3 79 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3578 : NodeCoverage93 [11] 11 82 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3570
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3571
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3572
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3573
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3574
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3575
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3576
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3577
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3579 : NodeCoverage93 [10,10,10,10,10,10,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3580 : NodeCoverage93 [10,10,10,10,10,10,10,10,9] 9 4 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3581 : NodeCoverage93 [10,10,10,10,10,10,10,10,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3582 : NodeCoverage93 [10,10,10,10,10,10,10,10,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3583 : NodeCoverage93 [10,10,10,10,10,10,10,10,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3584 : NodeCoverage93 [10,10,10,10,10,10,10,10,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3585 : NodeCoverage93 [10,10,10,10,10,10,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3584
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3586 : NodeCoverage93 [10,10,10,10,10,10,10,10,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3587 : NodeCoverage93 [10,10,10,10,10,10,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3585
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3586
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3588 : NodeCoverage93 [10,10,10,10,10,10,10,10,3] 3 10 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3589 : NodeCoverage93 [10,10,10,10,10,10,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3579
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3580
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3581
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3582
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3583
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3587
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3588
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3590 : NodeCoverage93 [10,10,10,10,10,10,10,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3591 : NodeCoverage93 [10,10,10,10,10,10,10,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3592 : NodeCoverage93 [10,10,10,10,10,10,10,7] 7 16 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3593 : NodeCoverage93 [10,10,10,10,10,10,10,6] 6 17 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3594 : NodeCoverage93 [10,10,10,10,10,10,10,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3595 : NodeCoverage93 [10,10,10,10,10,10,10,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3594
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3596 : NodeCoverage93 [10,10,10,10,10,10,10,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3597 : NodeCoverage93 [10,10,10,10,10,10,10,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3595
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3596
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3598 : NodeCoverage93 [10,10,10,10,10,10,10,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3599 : NodeCoverage93 [10,10,10,10,10,10,10,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3597
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3598
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3600 : NodeCoverage93 [10,10,10,10,10,10,10,5,3] 3 15 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3601 : NodeCoverage93 [10,10,10,10,10,10,10,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3599
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3600
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3602 : NodeCoverage93 [10,10,10,10,10,10,10,3] 3 20 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3603 : NodeCoverage93 [10,10,10,10,10,10,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3589
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3590
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3591
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3592
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3593
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3601
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3602
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3604 : NodeCoverage93 [10,10,10,10,10,10,9] 9 24 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3605 : NodeCoverage93 [10,10,10,10,10,10,8] 8 25 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3606 : NodeCoverage93 [10,10,10,10,10,10,7] 7 26 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3607 : NodeCoverage93 [10,10,10,10,10,10,6] 6 27 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3608 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3609 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3608
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3610 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3611 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3609
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3610
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3612 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3613 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3611
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3612
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3614 : NodeCoverage93 [10,10,10,10,10,10,5,5,5,3] 3 15 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3615 : NodeCoverage93 [10,10,10,10,10,10,5,5,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3613
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3614
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3616 : NodeCoverage93 [10,10,10,10,10,10,5,5,3] 3 20 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3617 : NodeCoverage93 [10,10,10,10,10,10,5,5] 5 23 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3615
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3616
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3618 : NodeCoverage93 [10,10,10,10,10,10,5,3] 3 25 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3619 : NodeCoverage93 [10,10,10,10,10,10,5] 5 28 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3617
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3618
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3620 : NodeCoverage93 [10,10,10,10,10,10,3] 3 30 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3621 : NodeCoverage93 [10,10,10,10,10,10] 10 33 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3603
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3604
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3605
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3606
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3607
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3619
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3620
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3622 : NodeCoverage93 [10,10,10,10,10,9] 9 34 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3623 : NodeCoverage93 [10,10,10,10,10,8] 8 35 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3624 : NodeCoverage93 [10,10,10,10,10,7] 7 36 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3625 : NodeCoverage93 [10,10,10,10,10,6] 6 37 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3626 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3627 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3626
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3628 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3629 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3627
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3628
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3630 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3631 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3629
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3630
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3632 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5,3] 3 15 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3633 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3631
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3632
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3634 : NodeCoverage93 [10,10,10,10,10,5,5,5,5,3] 3 20 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3635 : NodeCoverage93 [10,10,10,10,10,5,5,5,5] 5 23 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3633
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3634
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3636 : NodeCoverage93 [10,10,10,10,10,5,5,5,3] 3 25 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3637 : NodeCoverage93 [10,10,10,10,10,5,5,5] 5 28 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3635
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3636
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3638 : NodeCoverage93 [10,10,10,10,10,5,5,3] 3 30 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3639 : NodeCoverage93 [10,10,10,10,10,5,5] 5 33 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3637
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3638
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3640 : NodeCoverage93 [10,10,10,10,10,5,3] 3 35 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3641 : NodeCoverage93 [10,10,10,10,10,5] 5 38 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3639
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3640
    ChildrenCoverage93.nil))

end Symconf93
