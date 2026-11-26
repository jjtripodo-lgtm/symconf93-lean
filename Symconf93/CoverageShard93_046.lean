module
public import Symconf93.CoverageShard93_045

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1627 : NodeCoverage93 [24,13,3] 3 53 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1628 : NodeCoverage93 [24,13] 13 56 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1618
    (ChildrenCoverage93.cons _ _ compact93_node_1619
    (ChildrenCoverage93.cons _ _ compact93_node_1620
    (ChildrenCoverage93.cons _ _ compact93_node_1621
    (ChildrenCoverage93.cons _ _ compact93_node_1622
    (ChildrenCoverage93.cons _ _ compact93_node_1623
    (ChildrenCoverage93.cons _ _ compact93_node_1624
    (ChildrenCoverage93.cons _ _ compact93_node_1625
    (ChildrenCoverage93.cons _ _ compact93_node_1626
    (ChildrenCoverage93.cons _ _ compact93_node_1627
    ChildrenCoverage93.nil))))))))))

theorem compact93_node_1629 : NodeCoverage93 [24,12,12,12,12,12,9] 9 0 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1630 : NodeCoverage93 [24,12,12,12,12,12,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1631 : NodeCoverage93 [24,12,12,12,12,12,5] 5 4 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1632 : NodeCoverage93 [24,12,12,12,12,12,3] 3 6 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1633 : NodeCoverage93 [24,12,12,12,12,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1629
    (ChildrenCoverage93.cons _ _ compact93_node_1630
    (ChildrenCoverage93.cons _ _ compact93_node_1631
    (ChildrenCoverage93.cons _ _ compact93_node_1632
    ChildrenCoverage93.nil))))

theorem compact93_node_1634 : NodeCoverage93 [24,12,12,12,12,11] 11 10 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1635 : NodeCoverage93 [24,12,12,12,12,10] 10 11 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1636 : NodeCoverage93 [24,12,12,12,12,9] 9 12 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1637 : NodeCoverage93 [24,12,12,12,12,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1638 : NodeCoverage93 [24,12,12,12,12,7] 7 14 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1639 : NodeCoverage93 [24,12,12,12,12,6] 6 15 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1640 : NodeCoverage93 [24,12,12,12,12,5] 5 16 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1641 : NodeCoverage93 [24,12,12,12,12,3] 3 18 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1642 : NodeCoverage93 [24,12,12,12,12] 12 21 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1633
    (ChildrenCoverage93.cons _ _ compact93_node_1634
    (ChildrenCoverage93.cons _ _ compact93_node_1635
    (ChildrenCoverage93.cons _ _ compact93_node_1636
    (ChildrenCoverage93.cons _ _ compact93_node_1637
    (ChildrenCoverage93.cons _ _ compact93_node_1638
    (ChildrenCoverage93.cons _ _ compact93_node_1639
    (ChildrenCoverage93.cons _ _ compact93_node_1640
    (ChildrenCoverage93.cons _ _ compact93_node_1641
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1643 : NodeCoverage93 [24,12,12,12,11] 11 22 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
