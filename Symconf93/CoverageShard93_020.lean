module
public import Symconf93.CoverageShard93_019

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1011 : NodeCoverage93 [30,30,15,9] 9 9 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1012 : NodeCoverage93 [30,30,15,8] 8 10 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1013 : NodeCoverage93 [30,30,15,7] 7 11 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1014 : NodeCoverage93 [30,30,15,6] 6 12 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1015 : NodeCoverage93 [30,30,15,5] 5 13 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1016 : NodeCoverage93 [30,30,15,3] 3 15 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1017 : NodeCoverage93 [30,30,15] 15 18 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1001
    (ChildrenCoverage93.cons _ _ compact93_node_1002
    (ChildrenCoverage93.cons _ _ compact93_node_1003
    (ChildrenCoverage93.cons _ _ compact93_node_1004
    (ChildrenCoverage93.cons _ _ compact93_node_1005
    (ChildrenCoverage93.cons _ _ compact93_node_1010
    (ChildrenCoverage93.cons _ _ compact93_node_1011
    (ChildrenCoverage93.cons _ _ compact93_node_1012
    (ChildrenCoverage93.cons _ _ compact93_node_1013
    (ChildrenCoverage93.cons _ _ compact93_node_1014
    (ChildrenCoverage93.cons _ _ compact93_node_1015
    (ChildrenCoverage93.cons _ _ compact93_node_1016
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_1018 : NodeCoverage93 [30,30,14] 14 19 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1019 : NodeCoverage93 [30,30,13] 13 20 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
