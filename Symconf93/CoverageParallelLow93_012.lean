module
public import Symconf93.CoverageParallelLow93_011

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2582 : NodeCoverage93 [18,9,9,9,9,9,9,9,3] 3 9 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2583 : NodeCoverage93 [18,9,9,9,9,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2577
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2578
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2579
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2580
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2581
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2582
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2584 : NodeCoverage93 [18,9,9,9,9,9,9,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2585 : NodeCoverage93 [18,9,9,9,9,9,9,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2586 : NodeCoverage93 [18,9,9,9,9,9,9,6] 6 15 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2587 : NodeCoverage93 [18,9,9,9,9,9,9,5] 5 16 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2588 : NodeCoverage93 [18,9,9,9,9,9,9,3] 3 18 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2589 : NodeCoverage93 [18,9,9,9,9,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2583
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2584
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2585
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2586
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2587
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2588
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2590 : NodeCoverage93 [18,9,9,9,9,9,8] 8 22 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2591 : NodeCoverage93 [18,9,9,9,9,9,7] 7 23 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2592 : NodeCoverage93 [18,9,9,9,9,9,6] 6 24 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2593 : NodeCoverage93 [18,9,9,9,9,9,5] 5 25 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2594 : NodeCoverage93 [18,9,9,9,9,9,3] 3 27 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2595 : NodeCoverage93 [18,9,9,9,9,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2589
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2590
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2591
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2592
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2593
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2594
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2596 : NodeCoverage93 [18,9,9,9,9,8] 8 31 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2597 : NodeCoverage93 [18,9,9,9,9,7] 7 32 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2598 : NodeCoverage93 [18,9,9,9,9,6] 6 33 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2599 : NodeCoverage93 [18,9,9,9,9,5] 5 34 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2600 : NodeCoverage93 [18,9,9,9,9,3] 3 36 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2601 : NodeCoverage93 [18,9,9,9,9] 9 39 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2595
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2596
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2597
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2598
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2599
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2600
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2602 : NodeCoverage93 [18,9,9,9,8] 8 40 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2603 : NodeCoverage93 [18,9,9,9,7] 7 41 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2604 : NodeCoverage93 [18,9,9,9,6] 6 42 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2605 : NodeCoverage93 [18,9,9,9,5] 5 43 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2606 : NodeCoverage93 [18,9,9,9,3] 3 45 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2607 : NodeCoverage93 [18,9,9,9] 9 48 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2601
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2602
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2603
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2604
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2605
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2606
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2608 : NodeCoverage93 [18,9,9,8] 8 49 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2609 : NodeCoverage93 [18,9,9,7] 7 50 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2610 : NodeCoverage93 [18,9,9,6] 6 51 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
