module
public import Symconf93.CoverageParallelLow93_034

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3913 : NodeCoverage93 [7] 7 86 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3909
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3910
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3911
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3912
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3914 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3915 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3914
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3916 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3917 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3918 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3917
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3919 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3918
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3920 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3915
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3916
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3919
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3921 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3922 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3923 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3922
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3924 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3923
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3925 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3924
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3926 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3925
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3927 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3920
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3921
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3926
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3928 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3929 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3930 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3929
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3931 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3930
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3932 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3931
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3933 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3932
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3934 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3933
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3935 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3934
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3936 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3927
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3928
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3935
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3937 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3938 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3939 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3938
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3940 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3939
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3941 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3940
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3942 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3941
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3943 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3942
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3944 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3943
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3945 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3944
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3946 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3945
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3947 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3936
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3937
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3946
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3948 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,5] 5 28 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3949 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3950 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3949
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3951 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3950
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3952 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3951
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3953 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3952
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3954 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3953
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3955 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3954
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3956 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3955
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3957 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3956
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3958 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3957
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3959 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3958
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3960 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,6] 6 33 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3947
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3948
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3959
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3961 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,5] 5 34 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3962 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3963 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3962
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3964 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3963
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3965 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3964
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3966 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3965
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3967 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3966
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3968 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3967
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3969 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3968
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3970 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3969
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3971 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3970
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3972 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3971
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3973 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3,3] 3 33 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3972
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3974 : NodeCoverage93 [6,6,6,6,6,6,6,6,6,3] 3 36 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3973
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3975 : NodeCoverage93 [6,6,6,6,6,6,6,6,6] 6 39 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3960
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3961
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3974
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3976 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,5,5,5,5] 5 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3977 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,5,5,5] 5 5 :=
  node_fork93 (B := [5]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3976
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3978 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,5,5,3] 3 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3979 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,5,5] 5 10 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3977
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3978
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3980 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,5,3] 3 12 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3981 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,5] 5 15 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3979
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3980
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3982 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5,3] 3 17 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3983 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,5] 5 20 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3981
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3982
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3984 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5,3] 3 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3985 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,5] 5 25 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3983
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3984
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3986 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5,3] 3 27 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3987 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,5] 5 30 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3985
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3986
    ChildrenCoverage93.nil))

end Symconf93
