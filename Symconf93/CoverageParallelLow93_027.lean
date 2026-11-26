module
public import Symconf93.CoverageParallelLow93_026

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3409 : NodeCoverage93 [12,11,5] 5 65 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3410 : NodeCoverage93 [12,11,3] 3 67 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3411 : NodeCoverage93 [12,11] 11 70 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3403
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3404
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3405
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3406
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3407
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3408
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3409
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3410
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_3412 : NodeCoverage93 [12,10,10,10] 10 51 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3413 : NodeCoverage93 [12,10,10,9] 9 52 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3414 : NodeCoverage93 [12,10,10,8] 8 53 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3415 : NodeCoverage93 [12,10,10,7] 7 54 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3416 : NodeCoverage93 [12,10,10,6] 6 55 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3417 : NodeCoverage93 [12,10,10,5] 5 56 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3418 : NodeCoverage93 [12,10,10,3] 3 58 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3419 : NodeCoverage93 [12,10,10] 10 61 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3412
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3413
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3414
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3415
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3416
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3417
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3418
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3420 : NodeCoverage93 [12,10,9] 9 62 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3421 : NodeCoverage93 [12,10,8] 8 63 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3422 : NodeCoverage93 [12,10,7] 7 64 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3423 : NodeCoverage93 [12,10,6] 6 65 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3424 : NodeCoverage93 [12,10,5] 5 66 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3425 : NodeCoverage93 [12,10,3] 3 68 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3426 : NodeCoverage93 [12,10] 10 71 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3419
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3420
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3421
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3422
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3423
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3424
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3425
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_3427 : NodeCoverage93 [12,9,9,9,9] 9 45 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3428 : NodeCoverage93 [12,9,9,9,8] 8 46 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3429 : NodeCoverage93 [12,9,9,9,7] 7 47 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3430 : NodeCoverage93 [12,9,9,9,6] 6 48 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3431 : NodeCoverage93 [12,9,9,9,5] 5 49 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3432 : NodeCoverage93 [12,9,9,9,3] 3 51 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3433 : NodeCoverage93 [12,9,9,9] 9 54 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3427
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3428
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3429
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3430
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3431
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3432
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3434 : NodeCoverage93 [12,9,9,8] 8 55 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3435 : NodeCoverage93 [12,9,9,7] 7 56 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3436 : NodeCoverage93 [12,9,9,6] 6 57 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3437 : NodeCoverage93 [12,9,9,5] 5 58 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3438 : NodeCoverage93 [12,9,9,3] 3 60 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3439 : NodeCoverage93 [12,9,9] 9 63 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3433
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3434
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3435
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3436
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3437
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3438
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3440 : NodeCoverage93 [12,9,8] 8 64 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3441 : NodeCoverage93 [12,9,7] 7 65 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3442 : NodeCoverage93 [12,9,6] 6 66 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3443 : NodeCoverage93 [12,9,5] 5 67 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
