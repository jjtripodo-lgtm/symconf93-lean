module
public import Symconf93.CoverageShard93_042

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1567 : NodeCoverage93 [24,24,12,12,10] 10 11 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1568 : NodeCoverage93 [24,24,12,12,9] 9 12 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1569 : NodeCoverage93 [24,24,12,12,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1570 : NodeCoverage93 [24,24,12,12,7] 7 14 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1571 : NodeCoverage93 [24,24,12,12,6] 6 15 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1572 : NodeCoverage93 [24,24,12,12,5] 5 16 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1573 : NodeCoverage93 [24,24,12,12,3] 3 18 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1574 : NodeCoverage93 [24,24,12,12] 12 21 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1565
    (ChildrenCoverage93.cons _ _ compact93_node_1566
    (ChildrenCoverage93.cons _ _ compact93_node_1567
    (ChildrenCoverage93.cons _ _ compact93_node_1568
    (ChildrenCoverage93.cons _ _ compact93_node_1569
    (ChildrenCoverage93.cons _ _ compact93_node_1570
    (ChildrenCoverage93.cons _ _ compact93_node_1571
    (ChildrenCoverage93.cons _ _ compact93_node_1572
    (ChildrenCoverage93.cons _ _ compact93_node_1573
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1575 : NodeCoverage93 [24,24,12,11] 11 22 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1576 : NodeCoverage93 [24,24,12,10] 10 23 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1577 : NodeCoverage93 [24,24,12,9] 9 24 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1578 : NodeCoverage93 [24,24,12,8] 8 25 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1579 : NodeCoverage93 [24,24,12,7] 7 26 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1580 : NodeCoverage93 [24,24,12,6,6,6,6,6,3] 3 0 :=
  node_no_weak_demand93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1581 : NodeCoverage93 [24,24,12,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1580
    ChildrenCoverage93.nil)

theorem compact93_node_1582 : NodeCoverage93 [24,24,12,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1583 : NodeCoverage93 [24,24,12,6,6,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1584 : NodeCoverage93 [24,24,12,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1583
    ChildrenCoverage93.nil)

theorem compact93_node_1585 : NodeCoverage93 [24,24,12,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1584
    ChildrenCoverage93.nil)

theorem compact93_node_1586 : NodeCoverage93 [24,24,12,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1581
    (ChildrenCoverage93.cons _ _ compact93_node_1582
    (ChildrenCoverage93.cons _ _ compact93_node_1585
    ChildrenCoverage93.nil)))

theorem compact93_node_1587 : NodeCoverage93 [24,24,12,6,6,6,5] 5 10 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1588 : NodeCoverage93 [24,24,12,6,6,6,3] 3 12 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1589 : NodeCoverage93 [24,24,12,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1586
    (ChildrenCoverage93.cons _ _ compact93_node_1587
    (ChildrenCoverage93.cons _ _ compact93_node_1588
    ChildrenCoverage93.nil)))

theorem compact93_node_1590 : NodeCoverage93 [24,24,12,6,6,5] 5 16 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
