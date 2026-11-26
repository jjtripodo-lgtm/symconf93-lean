module
public import Symconf93.CoverageShard93_046

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1644 : NodeCoverage93 [24,12,12,12,10] 10 23 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1645 : NodeCoverage93 [24,12,12,12,9] 9 24 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1646 : NodeCoverage93 [24,12,12,12,8] 8 25 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1647 : NodeCoverage93 [24,12,12,12,7] 7 26 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1648 : NodeCoverage93 [24,12,12,12,6,6,6,6,6,3] 3 0 :=
  node_no_weak_demand93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1649 : NodeCoverage93 [24,12,12,12,6,6,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1648
    ChildrenCoverage93.nil)

theorem compact93_node_1650 : NodeCoverage93 [24,12,12,12,6,6,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1651 : NodeCoverage93 [24,12,12,12,6,6,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1652 : NodeCoverage93 [24,12,12,12,6,6,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1651
    ChildrenCoverage93.nil)

theorem compact93_node_1653 : NodeCoverage93 [24,12,12,12,6,6,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1652
    ChildrenCoverage93.nil)

theorem compact93_node_1654 : NodeCoverage93 [24,12,12,12,6,6,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1649
    (ChildrenCoverage93.cons _ _ compact93_node_1650
    (ChildrenCoverage93.cons _ _ compact93_node_1653
    ChildrenCoverage93.nil)))

theorem compact93_node_1655 : NodeCoverage93 [24,12,12,12,6,6,6,5] 5 10 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1656 : NodeCoverage93 [24,12,12,12,6,6,6,3] 3 12 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1657 : NodeCoverage93 [24,12,12,12,6,6,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1654
    (ChildrenCoverage93.cons _ _ compact93_node_1655
    (ChildrenCoverage93.cons _ _ compact93_node_1656
    ChildrenCoverage93.nil)))

theorem compact93_node_1658 : NodeCoverage93 [24,12,12,12,6,6,5] 5 16 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1659 : NodeCoverage93 [24,12,12,12,6,6,3] 3 18 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1660 : NodeCoverage93 [24,12,12,12,6,6] 6 21 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1657
    (ChildrenCoverage93.cons _ _ compact93_node_1658
    (ChildrenCoverage93.cons _ _ compact93_node_1659
    ChildrenCoverage93.nil)))

theorem compact93_node_1661 : NodeCoverage93 [24,12,12,12,6,5] 5 22 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1662 : NodeCoverage93 [24,12,12,12,6,3] 3 24 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1663 : NodeCoverage93 [24,12,12,12,6] 6 27 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1660
    (ChildrenCoverage93.cons _ _ compact93_node_1661
    (ChildrenCoverage93.cons _ _ compact93_node_1662
    ChildrenCoverage93.nil)))

theorem compact93_node_1664 : NodeCoverage93 [24,12,12,12,5] 5 28 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1665 : NodeCoverage93 [24,12,12,12,3] 3 30 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1666 : NodeCoverage93 [24,12,12,12] 12 33 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1642
    (ChildrenCoverage93.cons _ _ compact93_node_1643
    (ChildrenCoverage93.cons _ _ compact93_node_1644
    (ChildrenCoverage93.cons _ _ compact93_node_1645
    (ChildrenCoverage93.cons _ _ compact93_node_1646
    (ChildrenCoverage93.cons _ _ compact93_node_1647
    (ChildrenCoverage93.cons _ _ compact93_node_1663
    (ChildrenCoverage93.cons _ _ compact93_node_1664
    (ChildrenCoverage93.cons _ _ compact93_node_1665
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1667 : NodeCoverage93 [24,12,12,11] 11 34 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1668 : NodeCoverage93 [24,12,12,10] 10 35 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1669 : NodeCoverage93 [24,12,12,9] 9 36 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1670 : NodeCoverage93 [24,12,12,8] 8 37 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
