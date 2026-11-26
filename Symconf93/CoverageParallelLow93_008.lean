module
public import Symconf93.CoverageParallelLow93_007

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2502 : NodeCoverage93 [18,18,3] 3 54 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2503 : NodeCoverage93 [18,18] 18 57 :=
  node_fork93 (B := [18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2425
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2426
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2427
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2428
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2429
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2430
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2431
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2432
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2433
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2497
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2498
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2499
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2500
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2501
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2502
    ChildrenCoverage93.nil)))))))))))))))

theorem compact_parallel93_node_2504 : NodeCoverage93 [18,17] 17 58 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2505 : NodeCoverage93 [18,16,16] 16 43 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2506 : NodeCoverage93 [18,16,15] 15 44 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2507 : NodeCoverage93 [18,16,14] 14 45 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2508 : NodeCoverage93 [18,16,13] 13 46 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2509 : NodeCoverage93 [18,16,12] 12 47 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2510 : NodeCoverage93 [18,16,11] 11 48 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2511 : NodeCoverage93 [18,16,10] 10 49 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2512 : NodeCoverage93 [18,16,9] 9 50 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2513 : NodeCoverage93 [18,16,8] 8 51 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2514 : NodeCoverage93 [18,16,7] 7 52 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2515 : NodeCoverage93 [18,16,6] 6 53 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2516 : NodeCoverage93 [18,16,5] 5 54 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2517 : NodeCoverage93 [18,16,3] 3 56 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2518 : NodeCoverage93 [18,16] 16 59 :=
  node_fork93 (B := [16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2505
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2506
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2507
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2508
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2509
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2510
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2511
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2512
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2513
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2514
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2515
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2516
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2517
    ChildrenCoverage93.nil)))))))))))))

theorem compact_parallel93_node_2519 : NodeCoverage93 [18,15,15] 15 45 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2520 : NodeCoverage93 [18,15,14] 14 46 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2521 : NodeCoverage93 [18,15,13] 13 47 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
