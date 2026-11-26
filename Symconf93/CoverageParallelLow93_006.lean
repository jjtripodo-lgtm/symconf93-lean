module
public import Symconf93.CoverageParallelLow93_005

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2428 : NodeCoverage93 [18,18,15] 15 42 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2429 : NodeCoverage93 [18,18,14] 14 43 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2430 : NodeCoverage93 [18,18,13] 13 44 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2431 : NodeCoverage93 [18,18,12] 12 45 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2432 : NodeCoverage93 [18,18,11] 11 46 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2433 : NodeCoverage93 [18,18,10] 10 47 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2434 : NodeCoverage93 [18,18,9,9,9,9,9,9] 9 3 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2435 : NodeCoverage93 [18,18,9,9,9,9,9,8] 8 4 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2436 : NodeCoverage93 [18,18,9,9,9,9,9,7] 7 5 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2437 : NodeCoverage93 [18,18,9,9,9,9,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2438 : NodeCoverage93 [18,18,9,9,9,9,9,5] 5 7 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2439 : NodeCoverage93 [18,18,9,9,9,9,9,3] 3 9 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2440 : NodeCoverage93 [18,18,9,9,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2434
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2435
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2436
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2437
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2438
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2439
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2441 : NodeCoverage93 [18,18,9,9,9,9,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2442 : NodeCoverage93 [18,18,9,9,9,9,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2443 : NodeCoverage93 [18,18,9,9,9,9,6,6,6,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2444 : NodeCoverage93 [18,18,9,9,9,9,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2443
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2445 : NodeCoverage93 [18,18,9,9,9,9,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2446 : NodeCoverage93 [18,18,9,9,9,9,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2447 : NodeCoverage93 [18,18,9,9,9,9,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2446
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2448 : NodeCoverage93 [18,18,9,9,9,9,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2447
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2449 : NodeCoverage93 [18,18,9,9,9,9,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2444
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2445
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2448
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2450 : NodeCoverage93 [18,18,9,9,9,9,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2451 : NodeCoverage93 [18,18,9,9,9,9,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2452 : NodeCoverage93 [18,18,9,9,9,9,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2451
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2453 : NodeCoverage93 [18,18,9,9,9,9,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2452
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2454 : NodeCoverage93 [18,18,9,9,9,9,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2453
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2455 : NodeCoverage93 [18,18,9,9,9,9,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2454
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2456 : NodeCoverage93 [18,18,9,9,9,9,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2449
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2450
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2455
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2457 : NodeCoverage93 [18,18,9,9,9,9,5] 5 16 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2458 : NodeCoverage93 [18,18,9,9,9,9,3] 3 18 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2459 : NodeCoverage93 [18,18,9,9,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2440
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2441
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2442
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2456
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2457
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2458
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2460 : NodeCoverage93 [18,18,9,9,9,8] 8 22 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2461 : NodeCoverage93 [18,18,9,9,9,7] 7 23 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2462 : NodeCoverage93 [18,18,9,9,9,6,6,6,6,6] 6 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2463 : NodeCoverage93 [18,18,9,9,9,6,6,6,6,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2464 : NodeCoverage93 [18,18,9,9,9,6,6,6,6,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2463
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2465 : NodeCoverage93 [18,18,9,9,9,6,6,6,6] 6 6 :=
  node_fork93 (B := [6,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2462
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2464
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2466 : NodeCoverage93 [18,18,9,9,9,6,6,6,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2467 : NodeCoverage93 [18,18,9,9,9,6,6,6,3,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2468 : NodeCoverage93 [18,18,9,9,9,6,6,6,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2467
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2469 : NodeCoverage93 [18,18,9,9,9,6,6,6,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2468
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2470 : NodeCoverage93 [18,18,9,9,9,6,6,6,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2469
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2471 : NodeCoverage93 [18,18,9,9,9,6,6,6] 6 12 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2465
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2466
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2470
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2472 : NodeCoverage93 [18,18,9,9,9,6,6,5] 5 13 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
