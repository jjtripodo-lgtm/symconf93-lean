module
public import Symconf93.CoverageParallelLow93_023

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3275 : NodeCoverage93 [12,12,11,11,11] 11 36 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3276 : NodeCoverage93 [12,12,11,11,10] 10 37 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3277 : NodeCoverage93 [12,12,11,11,9] 9 38 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3278 : NodeCoverage93 [12,12,11,11,8] 8 39 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3279 : NodeCoverage93 [12,12,11,11,7] 7 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3280 : NodeCoverage93 [12,12,11,11,6] 6 41 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3281 : NodeCoverage93 [12,12,11,11,5] 5 42 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3282 : NodeCoverage93 [12,12,11,11,3] 3 44 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3283 : NodeCoverage93 [12,12,11,11] 11 47 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3275
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3276
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3277
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3278
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3279
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3280
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3281
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3282
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3284 : NodeCoverage93 [12,12,11,10] 10 48 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3285 : NodeCoverage93 [12,12,11,9] 9 49 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3286 : NodeCoverage93 [12,12,11,8] 8 50 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3287 : NodeCoverage93 [12,12,11,7] 7 51 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3288 : NodeCoverage93 [12,12,11,6] 6 52 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3289 : NodeCoverage93 [12,12,11,5] 5 53 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3290 : NodeCoverage93 [12,12,11,3] 3 55 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3291 : NodeCoverage93 [12,12,11] 11 58 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3283
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3284
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3285
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3286
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3287
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3288
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3289
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3290
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3292 : NodeCoverage93 [12,12,10,10,10] 10 39 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3293 : NodeCoverage93 [12,12,10,10,9] 9 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3294 : NodeCoverage93 [12,12,10,10,8] 8 41 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3295 : NodeCoverage93 [12,12,10,10,7] 7 42 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3296 : NodeCoverage93 [12,12,10,10,6] 6 43 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3297 : NodeCoverage93 [12,12,10,10,5] 5 44 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3298 : NodeCoverage93 [12,12,10,10,3] 3 46 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3299 : NodeCoverage93 [12,12,10,10] 10 49 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3292
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3293
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3294
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3295
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3296
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3297
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3298
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3300 : NodeCoverage93 [12,12,10,9] 9 50 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3301 : NodeCoverage93 [12,12,10,8] 8 51 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3302 : NodeCoverage93 [12,12,10,7] 7 52 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3303 : NodeCoverage93 [12,12,10,6] 6 53 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3304 : NodeCoverage93 [12,12,10,5] 5 54 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3305 : NodeCoverage93 [12,12,10,3] 3 56 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3306 : NodeCoverage93 [12,12,10] 10 59 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3299
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3300
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3301
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3302
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3303
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3304
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3305
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3307 : NodeCoverage93 [12,12,9,9,9,9] 9 33 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3308 : NodeCoverage93 [12,12,9,9,9,8] 8 34 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3309 : NodeCoverage93 [12,12,9,9,9,7] 7 35 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3310 : NodeCoverage93 [12,12,9,9,9,6] 6 36 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3311 : NodeCoverage93 [12,12,9,9,9,5] 5 37 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
