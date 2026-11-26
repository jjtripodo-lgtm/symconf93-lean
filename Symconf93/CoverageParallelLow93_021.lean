module
public import Symconf93.CoverageParallelLow93_020

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3067 : NodeCoverage93 [13,13,9] 9 58 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3068 : NodeCoverage93 [13,13,8] 8 59 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3069 : NodeCoverage93 [13,13,7] 7 60 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3070 : NodeCoverage93 [13,13,6] 6 61 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3071 : NodeCoverage93 [13,13,5] 5 62 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3072 : NodeCoverage93 [13,13,3] 3 64 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3073 : NodeCoverage93 [13,13] 13 67 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3063
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3064
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3065
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3066
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3067
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3068
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3069
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3070
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3071
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3072
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_3074 : NodeCoverage93 [13,12] 12 68 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3075 : NodeCoverage93 [13,11] 11 69 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3076 : NodeCoverage93 [13,10] 10 70 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3077 : NodeCoverage93 [13,9] 9 71 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3078 : NodeCoverage93 [13,8] 8 72 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3079 : NodeCoverage93 [13,7] 7 73 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3080 : NodeCoverage93 [13,6] 6 74 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3081 : NodeCoverage93 [13,5] 5 75 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3082 : NodeCoverage93 [13,3] 3 77 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3083 : NodeCoverage93 [13] 13 80 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3073
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3074
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3075
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3076
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3077
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3078
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3079
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3080
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3081
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3082
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_3084 : NodeCoverage93 [12,12,12,12,12,12,12,9] 9 0 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3085 : NodeCoverage93 [12,12,12,12,12,12,12,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3086 : NodeCoverage93 [12,12,12,12,12,12,12,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3087 : NodeCoverage93 [12,12,12,12,12,12,12,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3088 : NodeCoverage93 [12,12,12,12,12,12,12,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3087
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3089 : NodeCoverage93 [12,12,12,12,12,12,12,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3088
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3090 : NodeCoverage93 [12,12,12,12,12,12,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3084
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3085
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3086
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3089
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3091 : NodeCoverage93 [12,12,12,12,12,12,11] 11 10 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3092 : NodeCoverage93 [12,12,12,12,12,12,10] 10 11 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3093 : NodeCoverage93 [12,12,12,12,12,12,9] 9 12 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3094 : NodeCoverage93 [12,12,12,12,12,12,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3095 : NodeCoverage93 [12,12,12,12,12,12,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3096 : NodeCoverage93 [12,12,12,12,12,12,6,6,6,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3097 : NodeCoverage93 [12,12,12,12,12,12,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3096
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3098 : NodeCoverage93 [12,12,12,12,12,12,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3099 : NodeCoverage93 [12,12,12,12,12,12,6,6,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3100 : NodeCoverage93 [12,12,12,12,12,12,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3099
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3101 : NodeCoverage93 [12,12,12,12,12,12,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3100
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3102 : NodeCoverage93 [12,12,12,12,12,12,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3097
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3098
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3101
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3103 : NodeCoverage93 [12,12,12,12,12,12,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3104 : NodeCoverage93 [12,12,12,12,12,12,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3105 : NodeCoverage93 [12,12,12,12,12,12,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3104
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3106 : NodeCoverage93 [12,12,12,12,12,12,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3105
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3107 : NodeCoverage93 [12,12,12,12,12,12,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3106
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3108 : NodeCoverage93 [12,12,12,12,12,12,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3107
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3109 : NodeCoverage93 [12,12,12,12,12,12,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3102
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3103
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3108
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3110 : NodeCoverage93 [12,12,12,12,12,12,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3111 : NodeCoverage93 [12,12,12,12,12,12,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3112 : NodeCoverage93 [12,12,12,12,12,12,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3111
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3113 : NodeCoverage93 [12,12,12,12,12,12,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3112
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3114 : NodeCoverage93 [12,12,12,12,12,12,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3113
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3115 : NodeCoverage93 [12,12,12,12,12,12,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3114
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3116 : NodeCoverage93 [12,12,12,12,12,12,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3115
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3117 : NodeCoverage93 [12,12,12,12,12,12,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3116
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3118 : NodeCoverage93 [12,12,12,12,12,12] 12 21 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3090
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3091
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3092
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3093
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3094
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3095
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3109
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3110
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3117
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_3119 : NodeCoverage93 [12,12,12,12,12,11] 11 22 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3120 : NodeCoverage93 [12,12,12,12,12,10] 10 23 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3121 : NodeCoverage93 [12,12,12,12,12,9] 9 24 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3122 : NodeCoverage93 [12,12,12,12,12,8] 8 25 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3123 : NodeCoverage93 [12,12,12,12,12,7] 7 26 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3124 : NodeCoverage93 [12,12,12,12,12,6,6,6,6,6,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3125 : NodeCoverage93 [12,12,12,12,12,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3124
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3126 : NodeCoverage93 [12,12,12,12,12,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3127 : NodeCoverage93 [12,12,12,12,12,6,6,6,6,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3128 : NodeCoverage93 [12,12,12,12,12,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3127
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3129 : NodeCoverage93 [12,12,12,12,12,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3128
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3130 : NodeCoverage93 [12,12,12,12,12,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3125
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3126
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3129
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3131 : NodeCoverage93 [12,12,12,12,12,6,6,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3132 : NodeCoverage93 [12,12,12,12,12,6,6,6,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3133 : NodeCoverage93 [12,12,12,12,12,6,6,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3132
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3134 : NodeCoverage93 [12,12,12,12,12,6,6,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3133
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3135 : NodeCoverage93 [12,12,12,12,12,6,6,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3134
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3136 : NodeCoverage93 [12,12,12,12,12,6,6,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3135
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3137 : NodeCoverage93 [12,12,12,12,12,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3130
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3131
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3136
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3138 : NodeCoverage93 [12,12,12,12,12,6,6,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3139 : NodeCoverage93 [12,12,12,12,12,6,6,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_3140 : NodeCoverage93 [12,12,12,12,12,6,6,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3139
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3141 : NodeCoverage93 [12,12,12,12,12,6,6,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3140
    ChildrenCoverage93.nil)

end Symconf93
