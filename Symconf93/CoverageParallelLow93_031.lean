module
public import Symconf93.CoverageParallelLow93_030

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3642 : NodeCoverage93 [10,10,10,10,10,3] 3 40 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3643 : NodeCoverage93 [10,10,10,10,10] 10 43 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3621
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3622
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3623
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3624
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3625
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3641
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3642
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3644 : NodeCoverage93 [10,10,10,10,9] 9 44 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3645 : NodeCoverage93 [10,10,10,10,8] 8 45 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3646 : NodeCoverage93 [10,10,10,10,7] 7 46 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3647 : NodeCoverage93 [10,10,10,10,6,6,6,6,6] 6 23 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3648 : NodeCoverage93 [10,10,10,10,6,6,6,6,5] 5 24 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3649 : NodeCoverage93 [10,10,10,10,6,6,6,6,3] 3 26 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3650 : NodeCoverage93 [10,10,10,10,6,6,6,6] 6 29 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3647
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3648
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3649
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3651 : NodeCoverage93 [10,10,10,10,6,6,6,5] 5 30 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3652 : NodeCoverage93 [10,10,10,10,6,6,6,3] 3 32 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3653 : NodeCoverage93 [10,10,10,10,6,6,6] 6 35 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3650
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3651
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3652
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3654 : NodeCoverage93 [10,10,10,10,6,6,5] 5 36 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3655 : NodeCoverage93 [10,10,10,10,6,6,3] 3 38 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3656 : NodeCoverage93 [10,10,10,10,6,6] 6 41 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3653
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3654
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3655
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3657 : NodeCoverage93 [10,10,10,10,6,5] 5 42 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3658 : NodeCoverage93 [10,10,10,10,6,3] 3 44 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3659 : NodeCoverage93 [10,10,10,10,6] 6 47 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3656
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3657
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3658
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3660 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3661 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3660
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3662 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3663 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3661
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3662
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3664 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3665 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3663
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3664
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3666 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5,3] 3 15 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3667 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3665
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3666
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3668 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5,3] 3 20 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3669 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,5] 5 23 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3667
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3668
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3670 : NodeCoverage93 [10,10,10,10,5,5,5,5,5,3] 3 25 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3671 : NodeCoverage93 [10,10,10,10,5,5,5,5,5] 5 28 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3669
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3670
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3672 : NodeCoverage93 [10,10,10,10,5,5,5,5,3] 3 30 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3673 : NodeCoverage93 [10,10,10,10,5,5,5,5] 5 33 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3671
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3672
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3674 : NodeCoverage93 [10,10,10,10,5,5,5,3] 3 35 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3675 : NodeCoverage93 [10,10,10,10,5,5,5] 5 38 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3673
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3674
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3676 : NodeCoverage93 [10,10,10,10,5,5,3] 3 40 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3677 : NodeCoverage93 [10,10,10,10,5,5] 5 43 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3675
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3676
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3678 : NodeCoverage93 [10,10,10,10,5,3] 3 45 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3679 : NodeCoverage93 [10,10,10,10,5] 5 48 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3677
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3678
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3680 : NodeCoverage93 [10,10,10,10,3] 3 50 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3681 : NodeCoverage93 [10,10,10,10] 10 53 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3643
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3644
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3645
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3646
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3659
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3679
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3680
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3682 : NodeCoverage93 [10,10,10,9,9,9,9] 9 27 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3683 : NodeCoverage93 [10,10,10,9,9,9,8] 8 28 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3684 : NodeCoverage93 [10,10,10,9,9,9,7] 7 29 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3685 : NodeCoverage93 [10,10,10,9,9,9,6] 6 30 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3686 : NodeCoverage93 [10,10,10,9,9,9,5] 5 31 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3687 : NodeCoverage93 [10,10,10,9,9,9,3] 3 33 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3688 : NodeCoverage93 [10,10,10,9,9,9] 9 36 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3682
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3683
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3684
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3685
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3686
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3687
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3689 : NodeCoverage93 [10,10,10,9,9,8] 8 37 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3690 : NodeCoverage93 [10,10,10,9,9,7] 7 38 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3691 : NodeCoverage93 [10,10,10,9,9,6] 6 39 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3692 : NodeCoverage93 [10,10,10,9,9,5] 5 40 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3693 : NodeCoverage93 [10,10,10,9,9,3] 3 42 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3694 : NodeCoverage93 [10,10,10,9,9] 9 45 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3688
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3689
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3690
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3691
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3692
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3693
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3695 : NodeCoverage93 [10,10,10,9,8] 8 46 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3696 : NodeCoverage93 [10,10,10,9,7] 7 47 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3697 : NodeCoverage93 [10,10,10,9,6] 6 48 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3698 : NodeCoverage93 [10,10,10,9,5] 5 49 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3699 : NodeCoverage93 [10,10,10,9,3] 3 51 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3700 : NodeCoverage93 [10,10,10,9] 9 54 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3694
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3695
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3696
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3697
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3698
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3699
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3701 : NodeCoverage93 [10,10,10,8] 8 55 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3702 : NodeCoverage93 [10,10,10,7,7,7,7,7] 7 28 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3703 : NodeCoverage93 [10,10,10,7,7,7,7,6] 6 29 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3704 : NodeCoverage93 [10,10,10,7,7,7,7,5] 5 30 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3705 : NodeCoverage93 [10,10,10,7,7,7,7,3] 3 32 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
