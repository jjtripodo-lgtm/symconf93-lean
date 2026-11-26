module
public import Symconf93.CoverageParallelLow93_022

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3216 : NodeCoverage93 [12,12,12,7,7,7,3] 3 33 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3217 : NodeCoverage93 [12,12,12,7,7,7] 7 36 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3213
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3214
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3215
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3216
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3218 : NodeCoverage93 [12,12,12,7,7,6] 6 37 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3219 : NodeCoverage93 [12,12,12,7,7,5] 5 38 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3220 : NodeCoverage93 [12,12,12,7,7,3] 3 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3221 : NodeCoverage93 [12,12,12,7,7] 7 43 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3217
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3218
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3219
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3220
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3222 : NodeCoverage93 [12,12,12,7,6] 6 44 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3223 : NodeCoverage93 [12,12,12,7,5] 5 45 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3224 : NodeCoverage93 [12,12,12,7,3] 3 47 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3225 : NodeCoverage93 [12,12,12,7] 7 50 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3221
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3222
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3223
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3224
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3226 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6,6,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3227 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3226
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3228 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3229 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3230 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3229
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3231 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3230
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3232 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3227
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3228
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3231
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3233 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3234 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3235 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3234
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3236 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3235
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3237 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3236
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3238 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3237
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3239 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3232
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3233
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3238
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3240 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3241 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3242 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3241
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3243 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3242
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3244 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3243
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3245 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3244
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3246 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3245
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3247 : NodeCoverage93 [12,12,12,6,6,6,6,6,6,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3246
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3248 : NodeCoverage93 [12,12,12,6,6,6,6,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3239
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3240
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3247
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3249 : NodeCoverage93 [12,12,12,6,6,6,6,6,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3250 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3251 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3250
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3252 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3251
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3253 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3252
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3254 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3253
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3255 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3254
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3256 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3255
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3257 : NodeCoverage93 [12,12,12,6,6,6,6,6,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3256
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3258 : NodeCoverage93 [12,12,12,6,6,6,6,6,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3257
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3259 : NodeCoverage93 [12,12,12,6,6,6,6,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3248
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3249
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3258
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3260 : NodeCoverage93 [12,12,12,6,6,6,6,5] 5 28 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3261 : NodeCoverage93 [12,12,12,6,6,6,6,3] 3 30 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3262 : NodeCoverage93 [12,12,12,6,6,6,6] 6 33 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3259
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3260
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3261
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3263 : NodeCoverage93 [12,12,12,6,6,6,5] 5 34 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3264 : NodeCoverage93 [12,12,12,6,6,6,3] 3 36 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3265 : NodeCoverage93 [12,12,12,6,6,6] 6 39 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3262
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3263
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3264
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3266 : NodeCoverage93 [12,12,12,6,6,5] 5 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3267 : NodeCoverage93 [12,12,12,6,6,3] 3 42 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3268 : NodeCoverage93 [12,12,12,6,6] 6 45 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3265
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3266
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3267
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3269 : NodeCoverage93 [12,12,12,6,5] 5 46 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3270 : NodeCoverage93 [12,12,12,6,3] 3 48 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3271 : NodeCoverage93 [12,12,12,6] 6 51 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3268
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3269
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3270
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3272 : NodeCoverage93 [12,12,12,5] 5 52 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3273 : NodeCoverage93 [12,12,12,3] 3 54 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3274 : NodeCoverage93 [12,12,12] 12 57 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3208
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3209
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3210
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3211
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3212
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3225
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3271
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3272
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3273
    ChildrenCoverage93.nil)))))))))

end Symconf93
