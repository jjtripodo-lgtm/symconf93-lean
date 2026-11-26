module
public import Symconf93.CoverageShard93_041

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1546 : NodeCoverage93 [24,24,24,3] 3 18 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1547 : NodeCoverage93 [24,24,24] 24 21 :=
  node_fork93 (B := [21,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1525
    (ChildrenCoverage93.cons _ _ compact93_node_1526
    (ChildrenCoverage93.cons _ _ compact93_node_1527
    (ChildrenCoverage93.cons _ _ compact93_node_1528
    (ChildrenCoverage93.cons _ _ compact93_node_1529
    (ChildrenCoverage93.cons _ _ compact93_node_1530
    (ChildrenCoverage93.cons _ _ compact93_node_1531
    (ChildrenCoverage93.cons _ _ compact93_node_1538
    (ChildrenCoverage93.cons _ _ compact93_node_1539
    (ChildrenCoverage93.cons _ _ compact93_node_1540
    (ChildrenCoverage93.cons _ _ compact93_node_1541
    (ChildrenCoverage93.cons _ _ compact93_node_1542
    (ChildrenCoverage93.cons _ _ compact93_node_1543
    (ChildrenCoverage93.cons _ _ compact93_node_1544
    (ChildrenCoverage93.cons _ _ compact93_node_1545
    (ChildrenCoverage93.cons _ _ compact93_node_1546
    ChildrenCoverage93.nil))))))))))))))))

theorem compact93_node_1548 : NodeCoverage93 [24,24,23] 23 22 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1549 : NodeCoverage93 [24,24,22] 22 23 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1550 : NodeCoverage93 [24,24,21] 21 24 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1551 : NodeCoverage93 [24,24,20] 20 25 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1552 : NodeCoverage93 [24,24,19] 19 26 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1553 : NodeCoverage93 [24,24,18] 18 27 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1554 : NodeCoverage93 [24,24,17] 17 28 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1555 : NodeCoverage93 [24,24,16] 16 29 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1556 : NodeCoverage93 [24,24,15] 15 30 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1557 : NodeCoverage93 [24,24,14] 14 31 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1558 : NodeCoverage93 [24,24,13] 13 32 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1559 : NodeCoverage93 [24,24,12,12,12,9] 9 0 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1560 : NodeCoverage93 [24,24,12,12,12,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1561 : NodeCoverage93 [24,24,12,12,12,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1562 : NodeCoverage93 [24,24,12,12,12,3,3,3] 3 0 :=
  node_no_weak_demand93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1563 : NodeCoverage93 [24,24,12,12,12,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1562
    ChildrenCoverage93.nil)

theorem compact93_node_1564 : NodeCoverage93 [24,24,12,12,12,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1563
    ChildrenCoverage93.nil)

theorem compact93_node_1565 : NodeCoverage93 [24,24,12,12,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1559
    (ChildrenCoverage93.cons _ _ compact93_node_1560
    (ChildrenCoverage93.cons _ _ compact93_node_1561
    (ChildrenCoverage93.cons _ _ compact93_node_1564
    ChildrenCoverage93.nil))))

theorem compact93_node_1566 : NodeCoverage93 [24,24,12,12,11] 11 10 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
