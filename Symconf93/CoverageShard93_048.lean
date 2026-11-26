module
public import Symconf93.CoverageShard93_047

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1671 : NodeCoverage93 [24,12,12,7] 7 38 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1672 : NodeCoverage93 [24,12,12,6] 6 39 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1673 : NodeCoverage93 [24,12,12,5] 5 40 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1674 : NodeCoverage93 [24,12,12,3] 3 42 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1675 : NodeCoverage93 [24,12,12] 12 45 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1666
    (ChildrenCoverage93.cons _ _ compact93_node_1667
    (ChildrenCoverage93.cons _ _ compact93_node_1668
    (ChildrenCoverage93.cons _ _ compact93_node_1669
    (ChildrenCoverage93.cons _ _ compact93_node_1670
    (ChildrenCoverage93.cons _ _ compact93_node_1671
    (ChildrenCoverage93.cons _ _ compact93_node_1672
    (ChildrenCoverage93.cons _ _ compact93_node_1673
    (ChildrenCoverage93.cons _ _ compact93_node_1674
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1676 : NodeCoverage93 [24,12,11] 11 46 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1677 : NodeCoverage93 [24,12,10] 10 47 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1678 : NodeCoverage93 [24,12,9] 9 48 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1679 : NodeCoverage93 [24,12,8] 8 49 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1680 : NodeCoverage93 [24,12,7] 7 50 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1681 : NodeCoverage93 [24,12,6] 6 51 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1682 : NodeCoverage93 [24,12,5] 5 52 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1683 : NodeCoverage93 [24,12,3] 3 54 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1684 : NodeCoverage93 [24,12] 12 57 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1675
    (ChildrenCoverage93.cons _ _ compact93_node_1676
    (ChildrenCoverage93.cons _ _ compact93_node_1677
    (ChildrenCoverage93.cons _ _ compact93_node_1678
    (ChildrenCoverage93.cons _ _ compact93_node_1679
    (ChildrenCoverage93.cons _ _ compact93_node_1680
    (ChildrenCoverage93.cons _ _ compact93_node_1681
    (ChildrenCoverage93.cons _ _ compact93_node_1682
    (ChildrenCoverage93.cons _ _ compact93_node_1683
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1685 : NodeCoverage93 [24,11,11] 11 47 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1686 : NodeCoverage93 [24,11,10] 10 48 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1687 : NodeCoverage93 [24,11,9] 9 49 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1688 : NodeCoverage93 [24,11,8] 8 50 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1689 : NodeCoverage93 [24,11,7] 7 51 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
