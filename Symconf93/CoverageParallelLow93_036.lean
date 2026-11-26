module
public import Symconf93.CoverageParallelLow93_035

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3988 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5,3] 3 32 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3989 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,5] 5 35 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3987
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3988
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3990 : NodeCoverage93 [6,6,6,6,6,6,6,6,5,3] 3 37 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3991 : NodeCoverage93 [6,6,6,6,6,6,6,6,5] 5 40 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3989
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3990
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_3992 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3993 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3992
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3994 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3993
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3995 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3994
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3996 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3995
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3997 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3996
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3998 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3997
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3999 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3998
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4000 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3999
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4001 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4000
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4002 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4001
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4003 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3,3] 3 33 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4002
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4004 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3,3] 3 36 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4003
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4005 : NodeCoverage93 [6,6,6,6,6,6,6,6,3,3] 3 39 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4004
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4006 : NodeCoverage93 [6,6,6,6,6,6,6,6,3] 3 42 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4005
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4007 : NodeCoverage93 [6,6,6,6,6,6,6,6] 6 45 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3975
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3991
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4006
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4008 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5,5,5,5] 5 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4009 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5,5,5,3] 3 8 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4010 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5,5,5] 5 11 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4008
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4009
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4011 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5,5,3] 3 13 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4012 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5,5] 5 16 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4010
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4011
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4013 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5,3] 3 18 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4014 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,5] 5 21 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4012
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4013
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4015 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5,3] 3 23 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4016 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,5] 5 26 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4014
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4015
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4017 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5,3] 3 28 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4018 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,5] 5 31 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4016
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4017
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4019 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5,3] 3 33 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4020 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,5] 5 36 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4018
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4019
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4021 : NodeCoverage93 [6,6,6,6,6,6,6,5,5,3] 3 38 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4022 : NodeCoverage93 [6,6,6,6,6,6,6,5,5] 5 41 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4020
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4021
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4023 : NodeCoverage93 [6,6,6,6,6,6,6,5,3] 3 43 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4024 : NodeCoverage93 [6,6,6,6,6,6,6,5] 5 46 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4022
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4023
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4025 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4026 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4025
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4027 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4026
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4028 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4027
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4029 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4028
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4030 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4029
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4031 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4030
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4032 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4031
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4033 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4032
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4034 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4033
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4035 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4034
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4036 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3,3] 3 33 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4035
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4037 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3,3] 3 36 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4036
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4038 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3,3] 3 39 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4037
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4039 : NodeCoverage93 [6,6,6,6,6,6,6,3,3,3] 3 42 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4038
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4040 : NodeCoverage93 [6,6,6,6,6,6,6,3,3] 3 45 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4039
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4041 : NodeCoverage93 [6,6,6,6,6,6,6,3] 3 48 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4040
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4042 : NodeCoverage93 [6,6,6,6,6,6,6] 6 51 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4007
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4024
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4041
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4043 : NodeCoverage93 [6,6,6,6,6,6,5] 5 52 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4044 : NodeCoverage93 [6,6,6,6,6,6,3] 3 54 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4045 : NodeCoverage93 [6,6,6,6,6,6] 6 57 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4042
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4043
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4044
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4046 : NodeCoverage93 [6,6,6,6,6,5] 5 58 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4047 : NodeCoverage93 [6,6,6,6,6,3] 3 60 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4048 : NodeCoverage93 [6,6,6,6,6] 6 63 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4045
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4046
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4047
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4049 : NodeCoverage93 [6,6,6,6,5] 5 64 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4050 : NodeCoverage93 [6,6,6,6,3] 3 66 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4051 : NodeCoverage93 [6,6,6,6] 6 69 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4048
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4049
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4050
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4052 : NodeCoverage93 [6,6,6,5] 5 70 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4053 : NodeCoverage93 [6,6,6,3] 3 72 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4054 : NodeCoverage93 [6,6,6] 6 75 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4051
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4052
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4053
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4055 : NodeCoverage93 [6,6,5] 5 76 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4056 : NodeCoverage93 [6,6,3] 3 78 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4057 : NodeCoverage93 [6,6] 6 81 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4054
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4055
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4056
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4058 : NodeCoverage93 [6,5] 5 82 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4059 : NodeCoverage93 [6,3] 3 84 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4060 : NodeCoverage93 [6] 6 87 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4057
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4058
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4059
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_4061 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4062 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4061
    ChildrenCoverage93.nil)

end Symconf93
