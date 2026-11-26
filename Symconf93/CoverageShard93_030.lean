module
public import Symconf93.CoverageShard93_029

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1101 : NodeCoverage93 [30,15,6] 6 42 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1102 : NodeCoverage93 [30,15,5] 5 43 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1103 : NodeCoverage93 [30,15,3] 3 45 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1104 : NodeCoverage93 [30,15] 15 48 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1092
    (ChildrenCoverage93.cons _ _ compact93_node_1093
    (ChildrenCoverage93.cons _ _ compact93_node_1094
    (ChildrenCoverage93.cons _ _ compact93_node_1095
    (ChildrenCoverage93.cons _ _ compact93_node_1096
    (ChildrenCoverage93.cons _ _ compact93_node_1097
    (ChildrenCoverage93.cons _ _ compact93_node_1098
    (ChildrenCoverage93.cons _ _ compact93_node_1099
    (ChildrenCoverage93.cons _ _ compact93_node_1100
    (ChildrenCoverage93.cons _ _ compact93_node_1101
    (ChildrenCoverage93.cons _ _ compact93_node_1102
    (ChildrenCoverage93.cons _ _ compact93_node_1103
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_1105 : NodeCoverage93 [30,14] 14 49 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1106 : NodeCoverage93 [30,13] 13 50 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1107 : NodeCoverage93 [30,12] 12 51 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1108 : NodeCoverage93 [30,11] 11 52 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1109 : NodeCoverage93 [30,10,10,10,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
