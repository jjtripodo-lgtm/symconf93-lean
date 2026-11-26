module
public import Symconf93.CoverageShard93_032

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1136 : NodeCoverage93 [30,10,10,10,7] 7 26 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1137 : NodeCoverage93 [30,10,10,10,6] 6 27 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1138 : NodeCoverage93 [30,10,10,10,5] 5 28 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1139 : NodeCoverage93 [30,10,10,10,3] 3 30 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1140 : NodeCoverage93 [30,10,10,10] 10 33 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1133
    (ChildrenCoverage93.cons _ _ compact93_node_1134
    (ChildrenCoverage93.cons _ _ compact93_node_1135
    (ChildrenCoverage93.cons _ _ compact93_node_1136
    (ChildrenCoverage93.cons _ _ compact93_node_1137
    (ChildrenCoverage93.cons _ _ compact93_node_1138
    (ChildrenCoverage93.cons _ _ compact93_node_1139
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1141 : NodeCoverage93 [30,10,10,9] 9 34 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1142 : NodeCoverage93 [30,10,10,8] 8 35 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1143 : NodeCoverage93 [30,10,10,7] 7 36 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
