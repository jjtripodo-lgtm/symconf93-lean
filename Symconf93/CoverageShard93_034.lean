module
public import Symconf93.CoverageShard93_033

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1144 : NodeCoverage93 [30,10,10,6] 6 37 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1145 : NodeCoverage93 [30,10,10,5] 5 38 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1146 : NodeCoverage93 [30,10,10,3] 3 40 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1147 : NodeCoverage93 [30,10,10] 10 43 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1140
    (ChildrenCoverage93.cons _ _ compact93_node_1141
    (ChildrenCoverage93.cons _ _ compact93_node_1142
    (ChildrenCoverage93.cons _ _ compact93_node_1143
    (ChildrenCoverage93.cons _ _ compact93_node_1144
    (ChildrenCoverage93.cons _ _ compact93_node_1145
    (ChildrenCoverage93.cons _ _ compact93_node_1146
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1148 : NodeCoverage93 [30,10,9] 9 44 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1149 : NodeCoverage93 [30,10,8] 8 45 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1150 : NodeCoverage93 [30,10,7] 7 46 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1151 : NodeCoverage93 [30,10,6] 6 47 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
