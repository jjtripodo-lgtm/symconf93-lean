module
public import Symconf93.CoverageShard93_030

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1110 : NodeCoverage93 [30,10,10,10,10,10,9] 9 4 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1111 : NodeCoverage93 [30,10,10,10,10,10,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1112 : NodeCoverage93 [30,10,10,10,10,10,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1113 : NodeCoverage93 [30,10,10,10,10,10,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1114 : NodeCoverage93 [30,10,10,10,10,10,5,5,3] 3 0 :=
  node_no_weak_demand93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1115 : NodeCoverage93 [30,10,10,10,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1114
    ChildrenCoverage93.nil)

theorem compact93_node_1116 : NodeCoverage93 [30,10,10,10,10,10,5,3] 3 5 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact93_node_1117 : NodeCoverage93 [30,10,10,10,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1115
    (ChildrenCoverage93.cons _ _ compact93_node_1116
    ChildrenCoverage93.nil))

theorem compact93_node_1118 : NodeCoverage93 [30,10,10,10,10,10,3] 3 10 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1119 : NodeCoverage93 [30,10,10,10,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1109
    (ChildrenCoverage93.cons _ _ compact93_node_1110
    (ChildrenCoverage93.cons _ _ compact93_node_1111
    (ChildrenCoverage93.cons _ _ compact93_node_1112
    (ChildrenCoverage93.cons _ _ compact93_node_1113
    (ChildrenCoverage93.cons _ _ compact93_node_1117
    (ChildrenCoverage93.cons _ _ compact93_node_1118
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1120 : NodeCoverage93 [30,10,10,10,10,9] 9 14 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1121 : NodeCoverage93 [30,10,10,10,10,8] 8 15 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1122 : NodeCoverage93 [30,10,10,10,10,7] 7 16 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1123 : NodeCoverage93 [30,10,10,10,10,6,6,6,5] 5 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1124 : NodeCoverage93 [30,10,10,10,10,6,6,6] 6 5 :=
  node_fork93 (B := [5]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1123
    ChildrenCoverage93.nil)

theorem compact93_node_1125 : NodeCoverage93 [30,10,10,10,10,6,6,5] 5 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
