module
public import Symconf93.CoverageShard93_027

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1086 : NodeCoverage93 [30,15,15,9] 9 24 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1087 : NodeCoverage93 [30,15,15,8] 8 25 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1088 : NodeCoverage93 [30,15,15,7] 7 26 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1089 : NodeCoverage93 [30,15,15,6] 6 27 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1090 : NodeCoverage93 [30,15,15,5] 5 28 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1091 : NodeCoverage93 [30,15,15,3] 3 30 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1092 : NodeCoverage93 [30,15,15] 15 33 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1080
    (ChildrenCoverage93.cons _ _ compact93_node_1081
    (ChildrenCoverage93.cons _ _ compact93_node_1082
    (ChildrenCoverage93.cons _ _ compact93_node_1083
    (ChildrenCoverage93.cons _ _ compact93_node_1084
    (ChildrenCoverage93.cons _ _ compact93_node_1085
    (ChildrenCoverage93.cons _ _ compact93_node_1086
    (ChildrenCoverage93.cons _ _ compact93_node_1087
    (ChildrenCoverage93.cons _ _ compact93_node_1088
    (ChildrenCoverage93.cons _ _ compact93_node_1089
    (ChildrenCoverage93.cons _ _ compact93_node_1090
    (ChildrenCoverage93.cons _ _ compact93_node_1091
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_1093 : NodeCoverage93 [30,15,14] 14 34 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
