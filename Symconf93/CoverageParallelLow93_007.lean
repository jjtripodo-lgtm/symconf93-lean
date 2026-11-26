module
public import Symconf93.CoverageParallelLow93_006

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2473 : NodeCoverage93 [18,18,9,9,9,6,6,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2474 : NodeCoverage93 [18,18,9,9,9,6,6,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2473
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2475 : NodeCoverage93 [18,18,9,9,9,6,6,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2474
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2476 : NodeCoverage93 [18,18,9,9,9,6,6,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2475
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2477 : NodeCoverage93 [18,18,9,9,9,6,6,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2476
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2478 : NodeCoverage93 [18,18,9,9,9,6,6,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2477
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2479 : NodeCoverage93 [18,18,9,9,9,6,6] 6 18 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2471
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2472
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2478
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2480 : NodeCoverage93 [18,18,9,9,9,6,5] 5 19 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2481 : NodeCoverage93 [18,18,9,9,9,6,3] 3 21 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2482 : NodeCoverage93 [18,18,9,9,9,6] 6 24 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2479
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2480
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2481
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2483 : NodeCoverage93 [18,18,9,9,9,5] 5 25 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2484 : NodeCoverage93 [18,18,9,9,9,3] 3 27 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2485 : NodeCoverage93 [18,18,9,9,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2459
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2460
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2461
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2482
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2483
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2484
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2486 : NodeCoverage93 [18,18,9,9,8] 8 31 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2487 : NodeCoverage93 [18,18,9,9,7] 7 32 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2488 : NodeCoverage93 [18,18,9,9,6] 6 33 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2489 : NodeCoverage93 [18,18,9,9,5] 5 34 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2490 : NodeCoverage93 [18,18,9,9,3] 3 36 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2491 : NodeCoverage93 [18,18,9,9] 9 39 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2485
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2486
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2487
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2488
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2489
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2490
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2492 : NodeCoverage93 [18,18,9,8] 8 40 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2493 : NodeCoverage93 [18,18,9,7] 7 41 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2494 : NodeCoverage93 [18,18,9,6] 6 42 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2495 : NodeCoverage93 [18,18,9,5] 5 43 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2496 : NodeCoverage93 [18,18,9,3] 3 45 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2497 : NodeCoverage93 [18,18,9] 9 48 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2491
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2492
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2493
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2494
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2495
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2496
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2498 : NodeCoverage93 [18,18,8] 8 49 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2499 : NodeCoverage93 [18,18,7] 7 50 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2500 : NodeCoverage93 [18,18,6] 6 51 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2501 : NodeCoverage93 [18,18,5] 5 52 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
