module
public import Symconf93.CoverageShard93_021

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1034 : NodeCoverage93 [30,30,10,8] 8 15 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1035 : NodeCoverage93 [30,30,10,7] 7 16 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1036 : NodeCoverage93 [30,30,10,6,6,6,5] 5 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1037 : NodeCoverage93 [30,30,10,6,6,6] 6 5 :=
  node_fork93 (B := [5]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1036
    ChildrenCoverage93.nil)

theorem compact93_node_1038 : NodeCoverage93 [30,30,10,6,6,5] 5 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1039 : NodeCoverage93 [30,30,10,6,6,3] 3 8 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1040 : NodeCoverage93 [30,30,10,6,6] 6 11 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1037
    (ChildrenCoverage93.cons _ _ compact93_node_1038
    (ChildrenCoverage93.cons _ _ compact93_node_1039
    ChildrenCoverage93.nil)))

theorem compact93_node_1041 : NodeCoverage93 [30,30,10,6,5] 5 12 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1042 : NodeCoverage93 [30,30,10,6,3] 3 14 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1043 : NodeCoverage93 [30,30,10,6] 6 17 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1040
    (ChildrenCoverage93.cons _ _ compact93_node_1041
    (ChildrenCoverage93.cons _ _ compact93_node_1042
    ChildrenCoverage93.nil)))

theorem compact93_node_1044 : NodeCoverage93 [30,30,10,5] 5 18 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1045 : NodeCoverage93 [30,30,10,3] 3 20 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1046 : NodeCoverage93 [30,30,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1032
    (ChildrenCoverage93.cons _ _ compact93_node_1033
    (ChildrenCoverage93.cons _ _ compact93_node_1034
    (ChildrenCoverage93.cons _ _ compact93_node_1035
    (ChildrenCoverage93.cons _ _ compact93_node_1043
    (ChildrenCoverage93.cons _ _ compact93_node_1044
    (ChildrenCoverage93.cons _ _ compact93_node_1045
    ChildrenCoverage93.nil)))))))

end Symconf93
