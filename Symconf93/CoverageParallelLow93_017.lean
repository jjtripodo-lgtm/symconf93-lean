module
public import Symconf93.CoverageParallelLow93_016

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2883 : NodeCoverage93 [15,15,15,14] 14 34 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2884 : NodeCoverage93 [15,15,15,13] 13 35 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2885 : NodeCoverage93 [15,15,15,12] 12 36 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2886 : NodeCoverage93 [15,15,15,11] 11 37 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2887 : NodeCoverage93 [15,15,15,10] 10 38 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2888 : NodeCoverage93 [15,15,15,9] 9 39 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2889 : NodeCoverage93 [15,15,15,8] 8 40 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2890 : NodeCoverage93 [15,15,15,7] 7 41 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2891 : NodeCoverage93 [15,15,15,6] 6 42 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2892 : NodeCoverage93 [15,15,15,5] 5 43 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2893 : NodeCoverage93 [15,15,15,3] 3 45 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2894 : NodeCoverage93 [15,15,15] 15 48 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2882
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2883
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2884
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2885
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2886
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2887
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2888
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2889
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2890
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2891
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2892
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2893
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2895 : NodeCoverage93 [15,15,14] 14 49 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2896 : NodeCoverage93 [15,15,13] 13 50 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2897 : NodeCoverage93 [15,15,12] 12 51 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2898 : NodeCoverage93 [15,15,11] 11 52 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2899 : NodeCoverage93 [15,15,10] 10 53 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
