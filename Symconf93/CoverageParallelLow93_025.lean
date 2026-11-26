module
public import Symconf93.CoverageParallelLow93_024

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3312 : NodeCoverage93 [12,12,9,9,9,3] 3 39 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3313 : NodeCoverage93 [12,12,9,9,9] 9 42 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3307
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3308
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3309
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3310
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3311
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3312
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3314 : NodeCoverage93 [12,12,9,9,8] 8 43 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3315 : NodeCoverage93 [12,12,9,9,7] 7 44 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3316 : NodeCoverage93 [12,12,9,9,6] 6 45 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3317 : NodeCoverage93 [12,12,9,9,5] 5 46 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3318 : NodeCoverage93 [12,12,9,9,3] 3 48 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3319 : NodeCoverage93 [12,12,9,9] 9 51 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3313
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3314
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3315
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3316
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3317
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3318
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3320 : NodeCoverage93 [12,12,9,8] 8 52 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3321 : NodeCoverage93 [12,12,9,7] 7 53 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3322 : NodeCoverage93 [12,12,9,6] 6 54 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3323 : NodeCoverage93 [12,12,9,5] 5 55 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3324 : NodeCoverage93 [12,12,9,3] 3 57 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3325 : NodeCoverage93 [12,12,9] 9 60 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3319
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3320
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3321
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3322
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3323
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3324
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3326 : NodeCoverage93 [12,12,8] 8 61 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3327 : NodeCoverage93 [12,12,7,7,7,7] 7 41 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3328 : NodeCoverage93 [12,12,7,7,7,6] 6 42 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3329 : NodeCoverage93 [12,12,7,7,7,5] 5 43 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3330 : NodeCoverage93 [12,12,7,7,7,3] 3 45 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3331 : NodeCoverage93 [12,12,7,7,7] 7 48 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3327
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3328
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3329
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3330
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3332 : NodeCoverage93 [12,12,7,7,6] 6 49 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3333 : NodeCoverage93 [12,12,7,7,5] 5 50 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3334 : NodeCoverage93 [12,12,7,7,3] 3 52 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3335 : NodeCoverage93 [12,12,7,7] 7 55 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3331
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3332
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3333
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3334
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3336 : NodeCoverage93 [12,12,7,6] 6 56 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3337 : NodeCoverage93 [12,12,7,5] 5 57 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3338 : NodeCoverage93 [12,12,7,3] 3 59 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3339 : NodeCoverage93 [12,12,7] 7 62 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3335
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3336
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3337
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3338
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3340 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6,6,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3341 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3340
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3342 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3343 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3344 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3343
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3345 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3344
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3346 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3341
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3342
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3345
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3347 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3348 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3349 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3348
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3350 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3349
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3351 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3350
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3352 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3351
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3353 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3346
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3347
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3352
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3354 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3355 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3356 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3355
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3357 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3356
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3358 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3357
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3359 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3358
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3360 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3359
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3361 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3360
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3362 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3353
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3354
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3361
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3363 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
