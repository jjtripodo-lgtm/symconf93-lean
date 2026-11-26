module
public import Symconf93.CoverageShard93_043

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1591 : NodeCoverage93 [24,24,12,6,6,3] 3 18 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1592 : NodeCoverage93 [24,24,12,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1589
    (ChildrenCoverage93.cons _ _ compact93_node_1590
    (ChildrenCoverage93.cons _ _ compact93_node_1591
    ChildrenCoverage93.nil)))

theorem compact93_node_1593 : NodeCoverage93 [24,24,12,6,5] 5 22 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1594 : NodeCoverage93 [24,24,12,6,3] 3 24 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1595 : NodeCoverage93 [24,24,12,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1592
    (ChildrenCoverage93.cons _ _ compact93_node_1593
    (ChildrenCoverage93.cons _ _ compact93_node_1594
    ChildrenCoverage93.nil)))

theorem compact93_node_1596 : NodeCoverage93 [24,24,12,5] 5 28 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1597 : NodeCoverage93 [24,24,12,3] 3 30 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1598 : NodeCoverage93 [24,24,12] 12 33 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1574
    (ChildrenCoverage93.cons _ _ compact93_node_1575
    (ChildrenCoverage93.cons _ _ compact93_node_1576
    (ChildrenCoverage93.cons _ _ compact93_node_1577
    (ChildrenCoverage93.cons _ _ compact93_node_1578
    (ChildrenCoverage93.cons _ _ compact93_node_1579
    (ChildrenCoverage93.cons _ _ compact93_node_1595
    (ChildrenCoverage93.cons _ _ compact93_node_1596
    (ChildrenCoverage93.cons _ _ compact93_node_1597
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1599 : NodeCoverage93 [24,24,11] 11 34 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1600 : NodeCoverage93 [24,24,10] 10 35 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1601 : NodeCoverage93 [24,24,9] 9 36 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1602 : NodeCoverage93 [24,24,8] 8 37 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1603 : NodeCoverage93 [24,24,7] 7 38 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1604 : NodeCoverage93 [24,24,6] 6 39 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1605 : NodeCoverage93 [24,24,5] 5 40 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1606 : NodeCoverage93 [24,24,3] 3 42 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1607 : NodeCoverage93 [24,24] 24 45 :=
  node_fork93 (B := [24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1547
    (ChildrenCoverage93.cons _ _ compact93_node_1548
    (ChildrenCoverage93.cons _ _ compact93_node_1549
    (ChildrenCoverage93.cons _ _ compact93_node_1550
    (ChildrenCoverage93.cons _ _ compact93_node_1551
    (ChildrenCoverage93.cons _ _ compact93_node_1552
    (ChildrenCoverage93.cons _ _ compact93_node_1553
    (ChildrenCoverage93.cons _ _ compact93_node_1554
    (ChildrenCoverage93.cons _ _ compact93_node_1555
    (ChildrenCoverage93.cons _ _ compact93_node_1556
    (ChildrenCoverage93.cons _ _ compact93_node_1557
    (ChildrenCoverage93.cons _ _ compact93_node_1558
    (ChildrenCoverage93.cons _ _ compact93_node_1598
    (ChildrenCoverage93.cons _ _ compact93_node_1599
    (ChildrenCoverage93.cons _ _ compact93_node_1600
    (ChildrenCoverage93.cons _ _ compact93_node_1601
    (ChildrenCoverage93.cons _ _ compact93_node_1602
    (ChildrenCoverage93.cons _ _ compact93_node_1603
    (ChildrenCoverage93.cons _ _ compact93_node_1604
    (ChildrenCoverage93.cons _ _ compact93_node_1605
    (ChildrenCoverage93.cons _ _ compact93_node_1606
    ChildrenCoverage93.nil)))))))))))))))))))))

theorem compact93_node_1608 : NodeCoverage93 [24,23] 23 46 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1609 : NodeCoverage93 [24,22] 22 47 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1610 : NodeCoverage93 [24,21] 21 48 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
