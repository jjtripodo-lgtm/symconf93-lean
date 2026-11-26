module
public import Symconf93.CoverageShard93_020

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1020 : NodeCoverage93 [30,30,12] 12 21 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1021 : NodeCoverage93 [30,30,11] 11 22 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1022 : NodeCoverage93 [30,30,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1023 : NodeCoverage93 [30,30,10,10,9] 9 4 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1024 : NodeCoverage93 [30,30,10,10,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1025 : NodeCoverage93 [30,30,10,10,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1026 : NodeCoverage93 [30,30,10,10,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1027 : NodeCoverage93 [30,30,10,10,5,5,3] 3 0 :=
  node_no_weak_demand93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1028 : NodeCoverage93 [30,30,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1027
    ChildrenCoverage93.nil)

theorem compact93_node_1029 : NodeCoverage93 [30,30,10,10,5,3] 3 5 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact93_node_1030 : NodeCoverage93 [30,30,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1028
    (ChildrenCoverage93.cons _ _ compact93_node_1029
    ChildrenCoverage93.nil))

theorem compact93_node_1031 : NodeCoverage93 [30,30,10,10,3] 3 10 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1032 : NodeCoverage93 [30,30,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1022
    (ChildrenCoverage93.cons _ _ compact93_node_1023
    (ChildrenCoverage93.cons _ _ compact93_node_1024
    (ChildrenCoverage93.cons _ _ compact93_node_1025
    (ChildrenCoverage93.cons _ _ compact93_node_1026
    (ChildrenCoverage93.cons _ _ compact93_node_1030
    (ChildrenCoverage93.cons _ _ compact93_node_1031
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1033 : NodeCoverage93 [30,30,10,9] 9 14 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
