module
public import Symconf93.CoverageParallelLow93_021

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3142 : NodeCoverage93 [12,12,12,12,12,6,6,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3141
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3143 : NodeCoverage93 [12,12,12,12,12,6,6,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3142
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3144 : NodeCoverage93 [12,12,12,12,12,6,6,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3143
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3145 : NodeCoverage93 [12,12,12,12,12,6,6,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3144
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3146 : NodeCoverage93 [12,12,12,12,12,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3137
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3138
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3145
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3147 : NodeCoverage93 [12,12,12,12,12,6,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3148 : NodeCoverage93 [12,12,12,12,12,6,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3149 : NodeCoverage93 [12,12,12,12,12,6,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3148
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3150 : NodeCoverage93 [12,12,12,12,12,6,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3149
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3151 : NodeCoverage93 [12,12,12,12,12,6,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3150
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3152 : NodeCoverage93 [12,12,12,12,12,6,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3151
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3153 : NodeCoverage93 [12,12,12,12,12,6,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3152
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3154 : NodeCoverage93 [12,12,12,12,12,6,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3153
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3155 : NodeCoverage93 [12,12,12,12,12,6,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3154
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3156 : NodeCoverage93 [12,12,12,12,12,6,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3155
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3157 : NodeCoverage93 [12,12,12,12,12,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3146
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3147
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3156
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3158 : NodeCoverage93 [12,12,12,12,12,5] 5 28 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3159 : NodeCoverage93 [12,12,12,12,12,3] 3 30 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3160 : NodeCoverage93 [12,12,12,12,12] 12 33 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3118
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3119
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3120
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3121
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3122
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3123
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3157
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3158
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3159
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_3161 : NodeCoverage93 [12,12,12,12,11] 11 34 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3162 : NodeCoverage93 [12,12,12,12,10] 10 35 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3163 : NodeCoverage93 [12,12,12,12,9] 9 36 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3164 : NodeCoverage93 [12,12,12,12,8] 8 37 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3165 : NodeCoverage93 [12,12,12,12,7] 7 38 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3166 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6,6,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3167 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3166
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3168 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3169 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3170 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3169
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3171 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3170
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3172 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3167
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3168
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3171
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3173 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3174 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3175 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3174
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3176 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3175
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3177 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3176
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3178 : NodeCoverage93 [12,12,12,12,6,6,6,6,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3177
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3179 : NodeCoverage93 [12,12,12,12,6,6,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3172
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3173
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3178
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3180 : NodeCoverage93 [12,12,12,12,6,6,6,6,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3181 : NodeCoverage93 [12,12,12,12,6,6,6,6,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3182 : NodeCoverage93 [12,12,12,12,6,6,6,6,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3181
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3183 : NodeCoverage93 [12,12,12,12,6,6,6,6,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3182
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3184 : NodeCoverage93 [12,12,12,12,6,6,6,6,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3183
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3185 : NodeCoverage93 [12,12,12,12,6,6,6,6,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3184
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3186 : NodeCoverage93 [12,12,12,12,6,6,6,6,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3185
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3187 : NodeCoverage93 [12,12,12,12,6,6,6,6,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3186
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3188 : NodeCoverage93 [12,12,12,12,6,6,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3179
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3180
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3187
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3189 : NodeCoverage93 [12,12,12,12,6,6,6,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3190 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3191 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3190
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3192 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3191
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3193 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3192
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3194 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3193
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3195 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3194
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3196 : NodeCoverage93 [12,12,12,12,6,6,6,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3195
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3197 : NodeCoverage93 [12,12,12,12,6,6,6,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3196
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3198 : NodeCoverage93 [12,12,12,12,6,6,6,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3197
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3199 : NodeCoverage93 [12,12,12,12,6,6,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3188
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3189
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3198
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3200 : NodeCoverage93 [12,12,12,12,6,6,5] 5 28 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3201 : NodeCoverage93 [12,12,12,12,6,6,3] 3 30 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3202 : NodeCoverage93 [12,12,12,12,6,6] 6 33 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3199
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3200
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3201
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3203 : NodeCoverage93 [12,12,12,12,6,5] 5 34 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3204 : NodeCoverage93 [12,12,12,12,6,3] 3 36 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3205 : NodeCoverage93 [12,12,12,12,6] 6 39 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3202
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3203
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3204
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3206 : NodeCoverage93 [12,12,12,12,5] 5 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3207 : NodeCoverage93 [12,12,12,12,3] 3 42 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3208 : NodeCoverage93 [12,12,12,12] 12 45 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3160
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3161
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3162
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3163
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3164
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3165
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3205
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3206
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3207
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_3209 : NodeCoverage93 [12,12,12,11] 11 46 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3210 : NodeCoverage93 [12,12,12,10] 10 47 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3211 : NodeCoverage93 [12,12,12,9] 9 48 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3212 : NodeCoverage93 [12,12,12,8] 8 49 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3213 : NodeCoverage93 [12,12,12,7,7,7,7] 7 29 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3214 : NodeCoverage93 [12,12,12,7,7,7,6] 6 30 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3215 : NodeCoverage93 [12,12,12,7,7,7,5] 5 31 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
