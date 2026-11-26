module
public import Symconf93.CoverageShard93_026

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1076 : NodeCoverage93 [30,15,15,15,7] 7 11 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1077 : NodeCoverage93 [30,15,15,15,6] 6 12 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1078 : NodeCoverage93 [30,15,15,15,5] 5 13 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1079 : NodeCoverage93 [30,15,15,15,3] 3 15 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1080 : NodeCoverage93 [30,15,15,15] 15 18 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1068
    (ChildrenCoverage93.cons _ _ compact93_node_1069
    (ChildrenCoverage93.cons _ _ compact93_node_1070
    (ChildrenCoverage93.cons _ _ compact93_node_1071
    (ChildrenCoverage93.cons _ _ compact93_node_1072
    (ChildrenCoverage93.cons _ _ compact93_node_1073
    (ChildrenCoverage93.cons _ _ compact93_node_1074
    (ChildrenCoverage93.cons _ _ compact93_node_1075
    (ChildrenCoverage93.cons _ _ compact93_node_1076
    (ChildrenCoverage93.cons _ _ compact93_node_1077
    (ChildrenCoverage93.cons _ _ compact93_node_1078
    (ChildrenCoverage93.cons _ _ compact93_node_1079
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_1081 : NodeCoverage93 [30,15,15,14] 14 19 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1082 : NodeCoverage93 [30,15,15,13] 13 20 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1083 : NodeCoverage93 [30,15,15,12] 12 21 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1084 : NodeCoverage93 [30,15,15,11] 11 22 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1085 : NodeCoverage93 [30,15,15,10] 10 23 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
