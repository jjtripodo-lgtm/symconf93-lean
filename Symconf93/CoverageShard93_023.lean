module
public import Symconf93.CoverageShard93_022

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1047 : NodeCoverage93 [30,30,9] 9 24 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1048 : NodeCoverage93 [30,30,8] 8 25 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1049 : NodeCoverage93 [30,30,7] 7 26 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1050 : NodeCoverage93 [30,30,6] 6 27 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1051 : NodeCoverage93 [30,30,5] 5 28 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1052 : NodeCoverage93 [30,30,3] 3 30 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1053 : NodeCoverage93 [30,30] 30 33 :=
  node_fork93 (B := [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0986
    (ChildrenCoverage93.cons _ _ compact93_node_0987
    (ChildrenCoverage93.cons _ _ compact93_node_0988
    (ChildrenCoverage93.cons _ _ compact93_node_0989
    (ChildrenCoverage93.cons _ _ compact93_node_0990
    (ChildrenCoverage93.cons _ _ compact93_node_0991
    (ChildrenCoverage93.cons _ _ compact93_node_0992
    (ChildrenCoverage93.cons _ _ compact93_node_0993
    (ChildrenCoverage93.cons _ _ compact93_node_0994
    (ChildrenCoverage93.cons _ _ compact93_node_0995
    (ChildrenCoverage93.cons _ _ compact93_node_0996
    (ChildrenCoverage93.cons _ _ compact93_node_0997
    (ChildrenCoverage93.cons _ _ compact93_node_0998
    (ChildrenCoverage93.cons _ _ compact93_node_0999
    (ChildrenCoverage93.cons _ _ compact93_node_1000
    (ChildrenCoverage93.cons _ _ compact93_node_1017
    (ChildrenCoverage93.cons _ _ compact93_node_1018
    (ChildrenCoverage93.cons _ _ compact93_node_1019
    (ChildrenCoverage93.cons _ _ compact93_node_1020
    (ChildrenCoverage93.cons _ _ compact93_node_1021
    (ChildrenCoverage93.cons _ _ compact93_node_1046
    (ChildrenCoverage93.cons _ _ compact93_node_1047
    (ChildrenCoverage93.cons _ _ compact93_node_1048
    (ChildrenCoverage93.cons _ _ compact93_node_1049
    (ChildrenCoverage93.cons _ _ compact93_node_1050
    (ChildrenCoverage93.cons _ _ compact93_node_1051
    (ChildrenCoverage93.cons _ _ compact93_node_1052
    ChildrenCoverage93.nil)))))))))))))))))))))))))))

theorem compact93_node_1054 : NodeCoverage93 [30,29] 29 34 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
