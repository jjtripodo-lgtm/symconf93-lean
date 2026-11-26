module
public import Symconf93.CoverageParallelLow93_031

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3706 : NodeCoverage93 [10,10,10,7,7,7,7] 7 35 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3702
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3703
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3704
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3705
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3707 : NodeCoverage93 [10,10,10,7,7,7,6] 6 36 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3708 : NodeCoverage93 [10,10,10,7,7,7,5] 5 37 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3709 : NodeCoverage93 [10,10,10,7,7,7,3] 3 39 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3710 : NodeCoverage93 [10,10,10,7,7,7] 7 42 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3706
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3707
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3708
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3709
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3711 : NodeCoverage93 [10,10,10,7,7,6] 6 43 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3712 : NodeCoverage93 [10,10,10,7,7,5] 5 44 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3713 : NodeCoverage93 [10,10,10,7,7,3] 3 46 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3714 : NodeCoverage93 [10,10,10,7,7] 7 49 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3710
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3711
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3712
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3713
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3715 : NodeCoverage93 [10,10,10,7,6] 6 50 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3716 : NodeCoverage93 [10,10,10,7,5] 5 51 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3717 : NodeCoverage93 [10,10,10,7,3] 3 53 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3718 : NodeCoverage93 [10,10,10,7] 7 56 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3714
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3715
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3716
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3717
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3719 : NodeCoverage93 [10,10,10,6,6,6,6,6] 6 33 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3720 : NodeCoverage93 [10,10,10,6,6,6,6,5] 5 34 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3721 : NodeCoverage93 [10,10,10,6,6,6,6,3] 3 36 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3722 : NodeCoverage93 [10,10,10,6,6,6,6] 6 39 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3719
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3720
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3721
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3723 : NodeCoverage93 [10,10,10,6,6,6,5] 5 40 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3724 : NodeCoverage93 [10,10,10,6,6,6,3] 3 42 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3725 : NodeCoverage93 [10,10,10,6,6,6] 6 45 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3722
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3723
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3724
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3726 : NodeCoverage93 [10,10,10,6,6,5] 5 46 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3727 : NodeCoverage93 [10,10,10,6,6,3] 3 48 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3728 : NodeCoverage93 [10,10,10,6,6] 6 51 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3725
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3726
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3727
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3729 : NodeCoverage93 [10,10,10,6,5] 5 52 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3730 : NodeCoverage93 [10,10,10,6,3] 3 54 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3731 : NodeCoverage93 [10,10,10,6] 6 57 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3728
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3729
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3730
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3732 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3733 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3732
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3734 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3735 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3733
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3734
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3736 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3737 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3735
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3736
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3738 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5,3] 3 15 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3739 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3737
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3738
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3740 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5,3] 3 20 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3741 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,5] 5 23 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3739
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3740
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3742 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5,3] 3 25 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3743 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,5] 5 28 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3741
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3742
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3744 : NodeCoverage93 [10,10,10,5,5,5,5,5,5,3] 3 30 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3745 : NodeCoverage93 [10,10,10,5,5,5,5,5,5] 5 33 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3743
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3744
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3746 : NodeCoverage93 [10,10,10,5,5,5,5,5,3] 3 35 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3747 : NodeCoverage93 [10,10,10,5,5,5,5,5] 5 38 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3745
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3746
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3748 : NodeCoverage93 [10,10,10,5,5,5,5,3] 3 40 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3749 : NodeCoverage93 [10,10,10,5,5,5,5] 5 43 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3747
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3748
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3750 : NodeCoverage93 [10,10,10,5,5,5,3] 3 45 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3751 : NodeCoverage93 [10,10,10,5,5,5] 5 48 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3749
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3750
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3752 : NodeCoverage93 [10,10,10,5,5,3] 3 50 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3753 : NodeCoverage93 [10,10,10,5,5] 5 53 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3751
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3752
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3754 : NodeCoverage93 [10,10,10,5,3] 3 55 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3755 : NodeCoverage93 [10,10,10,5] 5 58 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3753
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3754
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3756 : NodeCoverage93 [10,10,10,3] 3 60 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3757 : NodeCoverage93 [10,10,10] 10 63 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3681
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3700
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3701
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3718
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3731
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3755
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3756
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3758 : NodeCoverage93 [10,10,9] 9 64 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3759 : NodeCoverage93 [10,10,8] 8 65 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3760 : NodeCoverage93 [10,10,7] 7 66 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3761 : NodeCoverage93 [10,10,6] 6 67 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3762 : NodeCoverage93 [10,10,5] 5 68 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3763 : NodeCoverage93 [10,10,3] 3 70 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3764 : NodeCoverage93 [10,10] 10 73 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3757
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3758
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3759
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3760
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3761
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3762
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3763
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3765 : NodeCoverage93 [10,9] 9 74 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3766 : NodeCoverage93 [10,8] 8 75 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3767 : NodeCoverage93 [10,7] 7 76 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3768 : NodeCoverage93 [10,6] 6 77 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3769 : NodeCoverage93 [10,5] 5 78 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3770 : NodeCoverage93 [10,3] 3 80 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3771 : NodeCoverage93 [10] 10 83 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3764
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3765
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3766
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3767
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3768
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3769
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3770
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3772 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,9,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3773 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3772
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3774 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,8] 8 4 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3775 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,7] 7 5 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3776 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3777 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3778 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3779 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3778
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3780 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3779
    ChildrenCoverage93.nil)

end Symconf93
