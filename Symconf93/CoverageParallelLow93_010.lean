module
public import Symconf93.CoverageParallelLow93_009

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2541 : NodeCoverage93 [18,13,5] 5 57 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2542 : NodeCoverage93 [18,13,3] 3 59 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2543 : NodeCoverage93 [18,13] 13 62 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2533
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2534
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2535
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2536
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2537
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2538
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2539
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2540
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2541
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2542
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_2544 : NodeCoverage93 [18,12,12] 12 51 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2545 : NodeCoverage93 [18,12,11] 11 52 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2546 : NodeCoverage93 [18,12,10] 10 53 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2547 : NodeCoverage93 [18,12,9,9] 9 45 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2548 : NodeCoverage93 [18,12,9,8] 8 46 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2549 : NodeCoverage93 [18,12,9,7] 7 47 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2550 : NodeCoverage93 [18,12,9,6] 6 48 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2551 : NodeCoverage93 [18,12,9,5] 5 49 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2552 : NodeCoverage93 [18,12,9,3] 3 51 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2553 : NodeCoverage93 [18,12,9] 9 54 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2547
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2548
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2549
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2550
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2551
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2552
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2554 : NodeCoverage93 [18,12,8] 8 55 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2555 : NodeCoverage93 [18,12,7] 7 56 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2556 : NodeCoverage93 [18,12,6] 6 57 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2557 : NodeCoverage93 [18,12,5] 5 58 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2558 : NodeCoverage93 [18,12,3] 3 60 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2559 : NodeCoverage93 [18,12] 12 63 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2544
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2545
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2546
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2553
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2554
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2555
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2556
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2557
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2558
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_2560 : NodeCoverage93 [18,11,11] 11 53 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
