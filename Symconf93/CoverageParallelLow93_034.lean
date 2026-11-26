module
public import Symconf93.CoverageParallelLow93_033

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3838 : NodeCoverage93 [9,9,3] 3 72 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3839 : NodeCoverage93 [9,9] 9 75 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3833
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3834
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3835
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3836
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3837
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3838
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3840 : NodeCoverage93 [9,8] 8 76 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3841 : NodeCoverage93 [9,7] 7 77 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3842 : NodeCoverage93 [9,6] 6 78 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3843 : NodeCoverage93 [9,5] 5 79 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3844 : NodeCoverage93 [9,3] 3 81 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3845 : NodeCoverage93 [9] 9 84 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3839
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3840
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3841
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3842
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3843
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3844
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3846 : NodeCoverage93 [8] 8 85 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3847 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3848 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3849 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,7,3] 3 6 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3850 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3847
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3848
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3849
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3851 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3852 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3853 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7,3] 3 13 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3854 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3850
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3851
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3852
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3853
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3855 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,6] 6 17 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3856 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,5] 5 18 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3857 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7,3] 3 20 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3858 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3854
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3855
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3856
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3857
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3859 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,6] 6 24 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3860 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,5] 5 25 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3861 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3862 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3861
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3863 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3862
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3864 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3863
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3865 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3864
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3866 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3865
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3867 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3866
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3868 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3867
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3869 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3868
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3870 : NodeCoverage93 [7,7,7,7,7,7,7,7,7,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3869
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3871 : NodeCoverage93 [7,7,7,7,7,7,7,7,7] 7 30 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3858
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3859
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3860
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3870
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3872 : NodeCoverage93 [7,7,7,7,7,7,7,7,6] 6 31 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3873 : NodeCoverage93 [7,7,7,7,7,7,7,7,5] 5 32 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3874 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3,3,3,3] 3 4 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact_parallel93_node_3875 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3,3,3] 3 7 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3874
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3876 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3,3] 3 10 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3875
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3877 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3] 3 13 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3876
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3878 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3,3,3] 3 16 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3877
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3879 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3,3] 3 19 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3878
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3880 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3,3] 3 22 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3879
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3881 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3,3] 3 25 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3880
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3882 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3,3] 3 28 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3881
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3883 : NodeCoverage93 [7,7,7,7,7,7,7,7,3,3] 3 31 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3882
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3884 : NodeCoverage93 [7,7,7,7,7,7,7,7,3] 3 34 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3883
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3885 : NodeCoverage93 [7,7,7,7,7,7,7,7] 7 37 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3871
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3872
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3873
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3884
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3886 : NodeCoverage93 [7,7,7,7,7,7,7,6] 6 38 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3887 : NodeCoverage93 [7,7,7,7,7,7,7,5] 5 39 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3888 : NodeCoverage93 [7,7,7,7,7,7,7,3] 3 41 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3889 : NodeCoverage93 [7,7,7,7,7,7,7] 7 44 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3885
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3886
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3887
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3888
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3890 : NodeCoverage93 [7,7,7,7,7,7,6] 6 45 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3891 : NodeCoverage93 [7,7,7,7,7,7,5] 5 46 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3892 : NodeCoverage93 [7,7,7,7,7,7,3] 3 48 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3893 : NodeCoverage93 [7,7,7,7,7,7] 7 51 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3889
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3890
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3891
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3892
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3894 : NodeCoverage93 [7,7,7,7,7,6] 6 52 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3895 : NodeCoverage93 [7,7,7,7,7,5] 5 53 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3896 : NodeCoverage93 [7,7,7,7,7,3] 3 55 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3897 : NodeCoverage93 [7,7,7,7,7] 7 58 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3893
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3894
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3895
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3896
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3898 : NodeCoverage93 [7,7,7,7,6] 6 59 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3899 : NodeCoverage93 [7,7,7,7,5] 5 60 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3900 : NodeCoverage93 [7,7,7,7,3] 3 62 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3901 : NodeCoverage93 [7,7,7,7] 7 65 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3897
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3898
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3899
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3900
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3902 : NodeCoverage93 [7,7,7,6] 6 66 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3903 : NodeCoverage93 [7,7,7,5] 5 67 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3904 : NodeCoverage93 [7,7,7,3] 3 69 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3905 : NodeCoverage93 [7,7,7] 7 72 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3901
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3902
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3903
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3904
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3906 : NodeCoverage93 [7,7,6] 6 73 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3907 : NodeCoverage93 [7,7,5] 5 74 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3908 : NodeCoverage93 [7,7,3] 3 76 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3909 : NodeCoverage93 [7,7] 7 79 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3905
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3906
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3907
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3908
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3910 : NodeCoverage93 [7,6] 6 80 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3911 : NodeCoverage93 [7,5] 5 81 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3912 : NodeCoverage93 [7,3] 3 83 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
