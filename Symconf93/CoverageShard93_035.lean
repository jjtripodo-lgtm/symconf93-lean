module
public import Symconf93.CoverageShard93_034

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1152 : NodeCoverage93 [30,10,5] 5 48 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1153 : NodeCoverage93 [30,10,3] 3 50 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1154 : NodeCoverage93 [30,10] 10 53 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1147
    (ChildrenCoverage93.cons _ _ compact93_node_1148
    (ChildrenCoverage93.cons _ _ compact93_node_1149
    (ChildrenCoverage93.cons _ _ compact93_node_1150
    (ChildrenCoverage93.cons _ _ compact93_node_1151
    (ChildrenCoverage93.cons _ _ compact93_node_1152
    (ChildrenCoverage93.cons _ _ compact93_node_1153
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1155 : NodeCoverage93 [30,9] 9 54 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1156 : NodeCoverage93 [30,8] 8 55 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1157 : NodeCoverage93 [30,7] 7 56 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1158 : NodeCoverage93 [30,6] 6 57 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1159 : NodeCoverage93 [30,5] 5 58 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
