module
public import Symconf93.CoverageParallelLow93_032

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3781 : NodeCoverage93 [9,9,9,9,9,9,9,9,9,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3780
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3782 : NodeCoverage93 [9,9,9,9,9,9,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3773
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3774
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3775
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3776
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3777
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3781
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3783 : NodeCoverage93 [9,9,9,9,9,9,9,9,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3784 : NodeCoverage93 [9,9,9,9,9,9,9,9,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3785 : NodeCoverage93 [9,9,9,9,9,9,9,9,6] 6 15 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3786 : NodeCoverage93 [9,9,9,9,9,9,9,9,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3787 : NodeCoverage93 [9,9,9,9,9,9,9,9,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3788 : NodeCoverage93 [9,9,9,9,9,9,9,9,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3787
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3789 : NodeCoverage93 [9,9,9,9,9,9,9,9,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3788
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3790 : NodeCoverage93 [9,9,9,9,9,9,9,9,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3789
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3791 : NodeCoverage93 [9,9,9,9,9,9,9,9,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3790
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3792 : NodeCoverage93 [9,9,9,9,9,9,9,9,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3791
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3793 : NodeCoverage93 [9,9,9,9,9,9,9,9,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3792
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3794 : NodeCoverage93 [9,9,9,9,9,9,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3782
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3783
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3784
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3785
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3786
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3793
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3795 : NodeCoverage93 [9,9,9,9,9,9,9,8] 8 22 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3796 : NodeCoverage93 [9,9,9,9,9,9,9,7] 7 23 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3797 : NodeCoverage93 [9,9,9,9,9,9,9,6] 6 24 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3798 : NodeCoverage93 [9,9,9,9,9,9,9,5] 5 25 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3799 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3800 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3799
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3801 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3800
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3802 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3801
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3803 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3802
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3804 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3803
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3805 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3804
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3806 : NodeCoverage93 [9,9,9,9,9,9,9,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3805
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3807 : NodeCoverage93 [9,9,9,9,9,9,9,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3806
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3808 : NodeCoverage93 [9,9,9,9,9,9,9,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3807
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3809 : NodeCoverage93 [9,9,9,9,9,9,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3794
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3795
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3796
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3797
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3798
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3808
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3810 : NodeCoverage93 [9,9,9,9,9,9,8] 8 31 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3811 : NodeCoverage93 [9,9,9,9,9,9,7] 7 32 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3812 : NodeCoverage93 [9,9,9,9,9,9,6] 6 33 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3813 : NodeCoverage93 [9,9,9,9,9,9,5] 5 34 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3814 : NodeCoverage93 [9,9,9,9,9,9,3] 3 36 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3815 : NodeCoverage93 [9,9,9,9,9,9] 9 39 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3809
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3810
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3811
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3812
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3813
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3814
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3816 : NodeCoverage93 [9,9,9,9,9,8] 8 40 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3817 : NodeCoverage93 [9,9,9,9,9,7] 7 41 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3818 : NodeCoverage93 [9,9,9,9,9,6] 6 42 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3819 : NodeCoverage93 [9,9,9,9,9,5] 5 43 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3820 : NodeCoverage93 [9,9,9,9,9,3] 3 45 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3821 : NodeCoverage93 [9,9,9,9,9] 9 48 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3815
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3816
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3817
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3818
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3819
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3820
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3822 : NodeCoverage93 [9,9,9,9,8] 8 49 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3823 : NodeCoverage93 [9,9,9,9,7] 7 50 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3824 : NodeCoverage93 [9,9,9,9,6] 6 51 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3825 : NodeCoverage93 [9,9,9,9,5] 5 52 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3826 : NodeCoverage93 [9,9,9,9,3] 3 54 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3827 : NodeCoverage93 [9,9,9,9] 9 57 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3821
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3822
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3823
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3824
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3825
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3826
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3828 : NodeCoverage93 [9,9,9,8] 8 58 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3829 : NodeCoverage93 [9,9,9,7] 7 59 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3830 : NodeCoverage93 [9,9,9,6] 6 60 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3831 : NodeCoverage93 [9,9,9,5] 5 61 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3832 : NodeCoverage93 [9,9,9,3] 3 63 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3833 : NodeCoverage93 [9,9,9] 9 66 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3827
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3828
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3829
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3830
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3831
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3832
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3834 : NodeCoverage93 [9,9,8] 8 67 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3835 : NodeCoverage93 [9,9,7] 7 68 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3836 : NodeCoverage93 [9,9,6] 6 69 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3837 : NodeCoverage93 [9,9,5] 5 70 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
