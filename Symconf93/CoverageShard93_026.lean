module
public import Symconf93.CoverageShard93_025

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1069 : NodeCoverage93 [30,15,15,15,14] 14 4 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1070 : NodeCoverage93 [30,15,15,15,13] 13 5 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1071 : NodeCoverage93 [30,15,15,15,12] 12 6 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1072 : NodeCoverage93 [30,15,15,15,11] 11 7 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1073 : NodeCoverage93 [30,15,15,15,10] 10 8 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1074 : NodeCoverage93 [30,15,15,15,9] 9 9 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1075 : NodeCoverage93 [30,15,15,15,8] 8 10 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
