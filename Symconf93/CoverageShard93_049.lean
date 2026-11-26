module
public import Symconf93.CoverageShard93_048

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1690 : NodeCoverage93 [24,11,6] 6 52 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1691 : NodeCoverage93 [24,11,5] 5 53 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1692 : NodeCoverage93 [24,11,3] 3 55 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1693 : NodeCoverage93 [24,11] 11 58 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1685
    (ChildrenCoverage93.cons _ _ compact93_node_1686
    (ChildrenCoverage93.cons _ _ compact93_node_1687
    (ChildrenCoverage93.cons _ _ compact93_node_1688
    (ChildrenCoverage93.cons _ _ compact93_node_1689
    (ChildrenCoverage93.cons _ _ compact93_node_1690
    (ChildrenCoverage93.cons _ _ compact93_node_1691
    (ChildrenCoverage93.cons _ _ compact93_node_1692
    ChildrenCoverage93.nil))))))))

theorem compact93_node_1694 : NodeCoverage93 [24,10,10] 10 49 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1695 : NodeCoverage93 [24,10,9] 9 50 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1696 : NodeCoverage93 [24,10,8] 8 51 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1697 : NodeCoverage93 [24,10,7] 7 52 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1698 : NodeCoverage93 [24,10,6] 6 53 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1699 : NodeCoverage93 [24,10,5] 5 54 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1700 : NodeCoverage93 [24,10,3] 3 56 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1701 : NodeCoverage93 [24,10] 10 59 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1694
    (ChildrenCoverage93.cons _ _ compact93_node_1695
    (ChildrenCoverage93.cons _ _ compact93_node_1696
    (ChildrenCoverage93.cons _ _ compact93_node_1697
    (ChildrenCoverage93.cons _ _ compact93_node_1698
    (ChildrenCoverage93.cons _ _ compact93_node_1699
    (ChildrenCoverage93.cons _ _ compact93_node_1700
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1702 : NodeCoverage93 [24,9,9] 9 51 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1703 : NodeCoverage93 [24,9,8] 8 52 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1704 : NodeCoverage93 [24,9,7] 7 53 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1705 : NodeCoverage93 [24,9,6] 6 54 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
