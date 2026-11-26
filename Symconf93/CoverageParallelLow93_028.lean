module
public import Symconf93.CoverageParallelLow93_027

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_3444 : NodeCoverage93 [12,9,3] 3 69 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3445 : NodeCoverage93 [12,9] 9 72 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3439
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3440
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3441
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3442
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3443
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3444
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_3446 : NodeCoverage93 [12,8] 8 73 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3447 : NodeCoverage93 [12,7,7,7,7] 7 53 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3448 : NodeCoverage93 [12,7,7,7,6] 6 54 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3449 : NodeCoverage93 [12,7,7,7,5] 5 55 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3450 : NodeCoverage93 [12,7,7,7,3] 3 57 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3451 : NodeCoverage93 [12,7,7,7] 7 60 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3447
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3448
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3449
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3450
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3452 : NodeCoverage93 [12,7,7,6] 6 61 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3453 : NodeCoverage93 [12,7,7,5] 5 62 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3454 : NodeCoverage93 [12,7,7,3] 3 64 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3455 : NodeCoverage93 [12,7,7] 7 67 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3451
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3452
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3453
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3454
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3456 : NodeCoverage93 [12,7,6] 6 68 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3457 : NodeCoverage93 [12,7,5] 5 69 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3458 : NodeCoverage93 [12,7,3] 3 71 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3459 : NodeCoverage93 [12,7] 7 74 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3455
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3456
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3457
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3458
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_3460 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6,6,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3461 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3460
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3462 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3463 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3464 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3463
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3465 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3464
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3466 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3461
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3462
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3465
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3467 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3468 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3469 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3468
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3470 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3469
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3471 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3470
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3472 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3471
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3473 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3466
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3467
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3472
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3474 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,5] 5 16 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3475 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3476 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3475
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3477 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3476
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3478 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3477
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3479 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3478
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3480 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3479
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3481 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3480
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3482 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3473
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3474
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3481
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3483 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,5] 5 22 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3484 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3485 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3484
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3486 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3485
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3487 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3486
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3488 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3487
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3489 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3488
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3490 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3489
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3491 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3490
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3492 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3491
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_3493 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3482
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3483
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3492
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3494 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,5] 5 28 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3495 : NodeCoverage93 [12,6,6,6,6,6,6,6,6,3] 3 30 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3496 : NodeCoverage93 [12,6,6,6,6,6,6,6,6] 6 33 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3493
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3494
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3495
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3497 : NodeCoverage93 [12,6,6,6,6,6,6,6,5] 5 34 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3498 : NodeCoverage93 [12,6,6,6,6,6,6,6,3] 3 36 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3499 : NodeCoverage93 [12,6,6,6,6,6,6,6] 6 39 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3496
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3497
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3498
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3500 : NodeCoverage93 [12,6,6,6,6,6,6,5] 5 40 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3501 : NodeCoverage93 [12,6,6,6,6,6,6,3] 3 42 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3502 : NodeCoverage93 [12,6,6,6,6,6,6] 6 45 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3499
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3500
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3501
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_3503 : NodeCoverage93 [12,6,6,6,6,6,5] 5 46 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
