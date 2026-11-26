module
public import Symconf93.CoverageParallelLow93_036

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_4063 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4064 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4062
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4063
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4065 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4066 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4064
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4065
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4067 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 15 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4068 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4066
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4067
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4069 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 20 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4070 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,5] 5 23 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4068
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4069
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4071 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5,3] 3 25 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4072 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,5] 5 28 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4070
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4071
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4073 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_4074 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4073
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4075 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4074
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4076 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4075
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4077 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4076
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4078 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4077
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4079 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4078
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4080 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4079
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4081 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4080
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4082 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4081
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4083 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4082
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4084 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,5] 5 33 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4072
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4083
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4085 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3] 3 5 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact_parallel93_node_4086 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3] 3 8 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4085
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4087 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3] 3 11 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4086
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4088 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3] 3 14 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4087
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4089 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3] 3 17 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4088
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4090 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3] 3 20 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4089
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4091 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3,3] 3 23 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4090
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4092 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3,3] 3 26 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4091
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4093 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3,3] 3 29 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4092
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4094 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3,3] 3 32 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4093
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4095 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5,3] 3 35 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4094
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4096 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,5] 5 38 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4084
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4095
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4097 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 4 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact_parallel93_node_4098 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3] 3 7 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4097
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4099 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3] 3 10 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4098
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4100 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3] 3 13 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4099
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4101 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3] 3 16 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4100
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4102 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3] 3 19 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4101
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4103 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3] 3 22 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4102
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4104 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3,3] 3 25 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4103
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4105 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3,3] 3 28 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4104
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4106 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3,3] 3 31 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4105
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4107 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3,3] 3 34 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4106
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4108 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3,3] 3 37 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4107
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4109 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5,3] 3 40 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4108
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4110 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,5] 5 43 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4096
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4109
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4111 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_4112 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4111
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4113 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4112
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4114 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4113
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4115 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4114
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4116 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4115
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4117 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4116
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4118 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4117
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4119 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4118
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4120 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4119
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4121 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4120
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4122 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3,3] 3 33 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4121
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4123 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3,3] 3 36 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4122
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4124 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3,3] 3 39 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4123
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4125 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3,3] 3 42 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4124
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4126 : NodeCoverage93 [5,5,5,5,5,5,5,5,5,3] 3 45 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4125
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4127 : NodeCoverage93 [5,5,5,5,5,5,5,5,5] 5 48 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4110
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4126
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4128 : NodeCoverage93 [5,5,5,5,5,5,5,5,3] 3 50 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4129 : NodeCoverage93 [5,5,5,5,5,5,5,5] 5 53 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4127
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4128
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4130 : NodeCoverage93 [5,5,5,5,5,5,5,3] 3 55 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4131 : NodeCoverage93 [5,5,5,5,5,5,5] 5 58 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4129
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4130
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4132 : NodeCoverage93 [5,5,5,5,5,5,3] 3 60 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4133 : NodeCoverage93 [5,5,5,5,5,5] 5 63 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4131
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4132
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4134 : NodeCoverage93 [5,5,5,5,5,3] 3 65 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4135 : NodeCoverage93 [5,5,5,5,5] 5 68 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4133
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4134
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4136 : NodeCoverage93 [5,5,5,5,3] 3 70 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4137 : NodeCoverage93 [5,5,5,5] 5 73 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4135
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4136
    ChildrenCoverage93.nil))

end Symconf93
