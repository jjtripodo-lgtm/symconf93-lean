module
public import Symconf93.CoverageParallelLow93_025

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3364 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3365 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3364
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3366 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3365
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3367 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3366
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3368 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3367
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3369 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3368
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3370 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3369
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3371 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3370
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3372 : NodeCoverage93 [12,12,6,6,6,6,6,6,6,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3371
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3373 : NodeCoverage93 [12,12,6,6,6,6,6,6,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3362
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3363
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3372
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3374 : NodeCoverage93 [12,12,6,6,6,6,6,6,5] 5 28 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3375 : NodeCoverage93 [12,12,6,6,6,6,6,6,3] 3 30 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3376 : NodeCoverage93 [12,12,6,6,6,6,6,6] 6 33 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3373
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3374
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3375
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3377 : NodeCoverage93 [12,12,6,6,6,6,6,5] 5 34 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3378 : NodeCoverage93 [12,12,6,6,6,6,6,3] 3 36 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3379 : NodeCoverage93 [12,12,6,6,6,6,6] 6 39 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3376
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3377
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3378
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3380 : NodeCoverage93 [12,12,6,6,6,6,5] 5 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3381 : NodeCoverage93 [12,12,6,6,6,6,3] 3 42 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3382 : NodeCoverage93 [12,12,6,6,6,6] 6 45 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3379
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3380
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3381
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3383 : NodeCoverage93 [12,12,6,6,6,5] 5 46 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3384 : NodeCoverage93 [12,12,6,6,6,3] 3 48 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3385 : NodeCoverage93 [12,12,6,6,6] 6 51 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3382
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3383
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3384
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3386 : NodeCoverage93 [12,12,6,6,5] 5 52 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3387 : NodeCoverage93 [12,12,6,6,3] 3 54 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3388 : NodeCoverage93 [12,12,6,6] 6 57 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3385
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3386
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3387
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3389 : NodeCoverage93 [12,12,6,5] 5 58 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3390 : NodeCoverage93 [12,12,6,3] 3 60 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3391 : NodeCoverage93 [12,12,6] 6 63 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3388
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3389
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3390
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3392 : NodeCoverage93 [12,12,5] 5 64 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3393 : NodeCoverage93 [12,12,3] 3 66 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3394 : NodeCoverage93 [12,12] 12 69 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3274
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3291
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3306
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3325
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3326
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3339
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3391
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3392
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3393
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_3395 : NodeCoverage93 [12,11,11,11] 11 48 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3396 : NodeCoverage93 [12,11,11,10] 10 49 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3397 : NodeCoverage93 [12,11,11,9] 9 50 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3398 : NodeCoverage93 [12,11,11,8] 8 51 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3399 : NodeCoverage93 [12,11,11,7] 7 52 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3400 : NodeCoverage93 [12,11,11,6] 6 53 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3401 : NodeCoverage93 [12,11,11,5] 5 54 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3402 : NodeCoverage93 [12,11,11,3] 3 56 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3403 : NodeCoverage93 [12,11,11] 11 59 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3395
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3396
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3397
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3398
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3399
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3400
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3401
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3402
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3404 : NodeCoverage93 [12,11,10] 10 60 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3405 : NodeCoverage93 [12,11,9] 9 61 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3406 : NodeCoverage93 [12,11,8] 8 62 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3407 : NodeCoverage93 [12,11,7] 7 63 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3408 : NodeCoverage93 [12,11,6] 6 64 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
