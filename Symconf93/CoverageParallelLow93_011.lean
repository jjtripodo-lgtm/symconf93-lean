module
public import Symconf93.CoverageParallelLow93_010

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2561 : NodeCoverage93 [18,11,10] 10 54 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2562 : NodeCoverage93 [18,11,9] 9 55 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2563 : NodeCoverage93 [18,11,8] 8 56 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2564 : NodeCoverage93 [18,11,7] 7 57 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2565 : NodeCoverage93 [18,11,6] 6 58 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2566 : NodeCoverage93 [18,11,5] 5 59 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2567 : NodeCoverage93 [18,11,3] 3 61 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2568 : NodeCoverage93 [18,11] 11 64 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2560
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2561
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2562
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2563
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2564
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2565
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2566
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2567
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_2569 : NodeCoverage93 [18,10,10] 10 55 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2570 : NodeCoverage93 [18,10,9] 9 56 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2571 : NodeCoverage93 [18,10,8] 8 57 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2572 : NodeCoverage93 [18,10,7] 7 58 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2573 : NodeCoverage93 [18,10,6] 6 59 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2574 : NodeCoverage93 [18,10,5] 5 60 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2575 : NodeCoverage93 [18,10,3] 3 62 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2576 : NodeCoverage93 [18,10] 10 65 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2569
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2570
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2571
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2572
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2573
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2574
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2575
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2577 : NodeCoverage93 [18,9,9,9,9,9,9,9,9] 9 3 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2578 : NodeCoverage93 [18,9,9,9,9,9,9,9,8] 8 4 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2579 : NodeCoverage93 [18,9,9,9,9,9,9,9,7] 7 5 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2580 : NodeCoverage93 [18,9,9,9,9,9,9,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2581 : NodeCoverage93 [18,9,9,9,9,9,9,9,5] 5 7 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
