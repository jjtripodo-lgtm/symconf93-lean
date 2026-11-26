module
public import Symconf93.CoverageShard93_018

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1000 : NodeCoverage93 [30,30,16] 16 17 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1001 : NodeCoverage93 [30,30,15,15] 15 3 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1002 : NodeCoverage93 [30,30,15,14] 14 4 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1003 : NodeCoverage93 [30,30,15,13] 13 5 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1004 : NodeCoverage93 [30,30,15,12] 12 6 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1005 : NodeCoverage93 [30,30,15,11] 11 7 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1006 : NodeCoverage93 [30,30,15,10,8] 8 0 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1007 : NodeCoverage93 [30,30,15,10,5,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_1008 : NodeCoverage93 [30,30,15,10,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1007
    ChildrenCoverage93.nil)

theorem compact93_node_1009 : NodeCoverage93 [30,30,15,10,3] 3 5 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1010 : NodeCoverage93 [30,30,15,10] 10 8 :=
  node_fork93 (B := [8,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1006
    (ChildrenCoverage93.cons _ _ compact93_node_1008
    (ChildrenCoverage93.cons _ _ compact93_node_1009
    ChildrenCoverage93.nil)))

end Symconf93
