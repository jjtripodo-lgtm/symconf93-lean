module
public import Symconf93.CoverageShard93_016

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0977 : NodeCoverage93 [31,10] 10 52 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0978 : NodeCoverage93 [31,9] 9 53 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0979 : NodeCoverage93 [31,8] 8 54 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0980 : NodeCoverage93 [31,7] 7 55 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0981 : NodeCoverage93 [31,6] 6 56 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0982 : NodeCoverage93 [31,5] 5 57 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0983 : NodeCoverage93 [31,3] 3 59 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0984 : NodeCoverage93 [31] 31 62 :=
  node_fork93 (B := [31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0956
    (ChildrenCoverage93.cons _ _ compact93_node_0957
    (ChildrenCoverage93.cons _ _ compact93_node_0958
    (ChildrenCoverage93.cons _ _ compact93_node_0959
    (ChildrenCoverage93.cons _ _ compact93_node_0960
    (ChildrenCoverage93.cons _ _ compact93_node_0961
    (ChildrenCoverage93.cons _ _ compact93_node_0962
    (ChildrenCoverage93.cons _ _ compact93_node_0963
    (ChildrenCoverage93.cons _ _ compact93_node_0964
    (ChildrenCoverage93.cons _ _ compact93_node_0965
    (ChildrenCoverage93.cons _ _ compact93_node_0966
    (ChildrenCoverage93.cons _ _ compact93_node_0967
    (ChildrenCoverage93.cons _ _ compact93_node_0968
    (ChildrenCoverage93.cons _ _ compact93_node_0969
    (ChildrenCoverage93.cons _ _ compact93_node_0970
    (ChildrenCoverage93.cons _ _ compact93_node_0971
    (ChildrenCoverage93.cons _ _ compact93_node_0972
    (ChildrenCoverage93.cons _ _ compact93_node_0973
    (ChildrenCoverage93.cons _ _ compact93_node_0974
    (ChildrenCoverage93.cons _ _ compact93_node_0975
    (ChildrenCoverage93.cons _ _ compact93_node_0976
    (ChildrenCoverage93.cons _ _ compact93_node_0977
    (ChildrenCoverage93.cons _ _ compact93_node_0978
    (ChildrenCoverage93.cons _ _ compact93_node_0979
    (ChildrenCoverage93.cons _ _ compact93_node_0980
    (ChildrenCoverage93.cons _ _ compact93_node_0981
    (ChildrenCoverage93.cons _ _ compact93_node_0982
    (ChildrenCoverage93.cons _ _ compact93_node_0983
    ChildrenCoverage93.nil))))))))))))))))))))))))))))

theorem compact93_node_0985 : NodeCoverage93 [30,30,30,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_0986 : NodeCoverage93 [30,30,30] 30 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0985
    ChildrenCoverage93.nil)

theorem compact93_node_0987 : NodeCoverage93 [30,30,29] 29 4 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0988 : NodeCoverage93 [30,30,28] 28 5 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0989 : NodeCoverage93 [30,30,27] 27 6 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0990 : NodeCoverage93 [30,30,26] 26 7 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0991 : NodeCoverage93 [30,30,25] 25 8 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0992 : NodeCoverage93 [30,30,24] 24 9 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
