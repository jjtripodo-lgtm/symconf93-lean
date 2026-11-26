module
public import Symconf93.CoverageShard93_031

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1126 : NodeCoverage93 [30,10,10,10,10,6,6,3] 3 8 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1127 : NodeCoverage93 [30,10,10,10,10,6,6] 6 11 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1124
    (ChildrenCoverage93.cons _ _ compact93_node_1125
    (ChildrenCoverage93.cons _ _ compact93_node_1126
    ChildrenCoverage93.nil)))

theorem compact93_node_1128 : NodeCoverage93 [30,10,10,10,10,6,5] 5 12 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1129 : NodeCoverage93 [30,10,10,10,10,6,3] 3 14 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1130 : NodeCoverage93 [30,10,10,10,10,6] 6 17 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1127
    (ChildrenCoverage93.cons _ _ compact93_node_1128
    (ChildrenCoverage93.cons _ _ compact93_node_1129
    ChildrenCoverage93.nil)))

theorem compact93_node_1131 : NodeCoverage93 [30,10,10,10,10,5] 5 18 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1132 : NodeCoverage93 [30,10,10,10,10,3] 3 20 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1133 : NodeCoverage93 [30,10,10,10,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1119
    (ChildrenCoverage93.cons _ _ compact93_node_1120
    (ChildrenCoverage93.cons _ _ compact93_node_1121
    (ChildrenCoverage93.cons _ _ compact93_node_1122
    (ChildrenCoverage93.cons _ _ compact93_node_1130
    (ChildrenCoverage93.cons _ _ compact93_node_1131
    (ChildrenCoverage93.cons _ _ compact93_node_1132
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1134 : NodeCoverage93 [30,10,10,10,9] 9 24 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1135 : NodeCoverage93 [30,10,10,10,8] 8 25 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
