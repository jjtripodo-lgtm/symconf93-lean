module
public import Symconf93.CoverageParallelLow93_017

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2900 : NodeCoverage93 [15,15,9] 9 54 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2901 : NodeCoverage93 [15,15,8] 8 55 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2902 : NodeCoverage93 [15,15,7] 7 56 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2903 : NodeCoverage93 [15,15,6] 6 57 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2904 : NodeCoverage93 [15,15,5] 5 58 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2905 : NodeCoverage93 [15,15,3] 3 60 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2906 : NodeCoverage93 [15,15] 15 63 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2894
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2895
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2896
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2897
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2898
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2899
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2900
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2901
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2902
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2903
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2904
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2905
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2907 : NodeCoverage93 [15,14] 14 64 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2908 : NodeCoverage93 [15,13] 13 65 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2909 : NodeCoverage93 [15,12] 12 66 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2910 : NodeCoverage93 [15,11] 11 67 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2911 : NodeCoverage93 [15,10] 10 68 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2912 : NodeCoverage93 [15,9] 9 69 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2913 : NodeCoverage93 [15,8] 8 70 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2914 : NodeCoverage93 [15,7] 7 71 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2915 : NodeCoverage93 [15,6] 6 72 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2916 : NodeCoverage93 [15,5] 5 73 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
