module
public import Symconf93.CoverageShard93_028

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1094 : NodeCoverage93 [30,15,13] 13 35 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1095 : NodeCoverage93 [30,15,12] 12 36 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1096 : NodeCoverage93 [30,15,11] 11 37 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1097 : NodeCoverage93 [30,15,10] 10 38 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1098 : NodeCoverage93 [30,15,9] 9 39 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1099 : NodeCoverage93 [30,15,8] 8 40 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1100 : NodeCoverage93 [30,15,7] 7 41 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
