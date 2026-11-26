module
public import Symconf93.CoverageParallelLow93_008

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2522 : NodeCoverage93 [18,15,12] 12 48 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2523 : NodeCoverage93 [18,15,11] 11 49 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2524 : NodeCoverage93 [18,15,10] 10 50 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2525 : NodeCoverage93 [18,15,9] 9 51 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2526 : NodeCoverage93 [18,15,8] 8 52 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2527 : NodeCoverage93 [18,15,7] 7 53 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2528 : NodeCoverage93 [18,15,6] 6 54 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2529 : NodeCoverage93 [18,15,5] 5 55 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2530 : NodeCoverage93 [18,15,3] 3 57 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2531 : NodeCoverage93 [18,15] 15 60 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2519
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2520
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2521
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2522
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2523
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2524
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2525
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2526
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2527
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2528
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2529
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2530
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2532 : NodeCoverage93 [18,14] 14 61 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2533 : NodeCoverage93 [18,13,13] 13 49 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2534 : NodeCoverage93 [18,13,12] 12 50 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2535 : NodeCoverage93 [18,13,11] 11 51 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2536 : NodeCoverage93 [18,13,10] 10 52 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2537 : NodeCoverage93 [18,13,9] 9 53 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2538 : NodeCoverage93 [18,13,8] 8 54 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2539 : NodeCoverage93 [18,13,7] 7 55 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2540 : NodeCoverage93 [18,13,6] 6 56 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
