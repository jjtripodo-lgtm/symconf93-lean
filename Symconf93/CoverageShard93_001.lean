module
public import Symconf93.CoverageShard93_000

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0075 : NodeCoverage93 [63,9,8] 8 13 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0076 : NodeCoverage93 [63,9,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0077 : NodeCoverage93 [63,9,6] 6 15 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0078 : NodeCoverage93 [63,9,5] 5 16 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0079 : NodeCoverage93 [63,9,3] 3 18 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0080 : NodeCoverage93 [63,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0074
    (ChildrenCoverage93.cons _ _ compact93_node_0075
    (ChildrenCoverage93.cons _ _ compact93_node_0076
    (ChildrenCoverage93.cons _ _ compact93_node_0077
    (ChildrenCoverage93.cons _ _ compact93_node_0078
    (ChildrenCoverage93.cons _ _ compact93_node_0079
    ChildrenCoverage93.nil))))))

theorem compact93_node_0081 : NodeCoverage93 [63,8] 8 22 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0082 : NodeCoverage93 [63,7] 7 23 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0083 : NodeCoverage93 [63,6] 6 24 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0084 : NodeCoverage93 [63,5] 5 25 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0085 : NodeCoverage93 [63,3] 3 27 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0086 : NodeCoverage93 [63] 63 30 :=
  node_fork93 (B := [30,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0048
    (ChildrenCoverage93.cons _ _ compact93_node_0049
    (ChildrenCoverage93.cons _ _ compact93_node_0050
    (ChildrenCoverage93.cons _ _ compact93_node_0051
    (ChildrenCoverage93.cons _ _ compact93_node_0052
    (ChildrenCoverage93.cons _ _ compact93_node_0053
    (ChildrenCoverage93.cons _ _ compact93_node_0054
    (ChildrenCoverage93.cons _ _ compact93_node_0055
    (ChildrenCoverage93.cons _ _ compact93_node_0056
    (ChildrenCoverage93.cons _ _ compact93_node_0057
    (ChildrenCoverage93.cons _ _ compact93_node_0058
    (ChildrenCoverage93.cons _ _ compact93_node_0059
    (ChildrenCoverage93.cons _ _ compact93_node_0060
    (ChildrenCoverage93.cons _ _ compact93_node_0061
    (ChildrenCoverage93.cons _ _ compact93_node_0062
    (ChildrenCoverage93.cons _ _ compact93_node_0063
    (ChildrenCoverage93.cons _ _ compact93_node_0064
    (ChildrenCoverage93.cons _ _ compact93_node_0065
    (ChildrenCoverage93.cons _ _ compact93_node_0066
    (ChildrenCoverage93.cons _ _ compact93_node_0080
    (ChildrenCoverage93.cons _ _ compact93_node_0081
    (ChildrenCoverage93.cons _ _ compact93_node_0082
    (ChildrenCoverage93.cons _ _ compact93_node_0083
    (ChildrenCoverage93.cons _ _ compact93_node_0084
    (ChildrenCoverage93.cons _ _ compact93_node_0085
    ChildrenCoverage93.nil)))))))))))))))))))))))))

theorem compact93_node_0087 : NodeCoverage93 [62] 62 31 :=
  demand_node_prune93 62 compact93_demands_62 compact93_demands_62_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0088 : NodeCoverage93 [61] 61 32 :=
  demand_node_prune93 61 compact93_demands_61 compact93_demands_61_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0089 : NodeCoverage93 [60,33] 33 0 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0090 : NodeCoverage93 [60,30] 30 3 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0091 : NodeCoverage93 [60,29] 29 4 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0092 : NodeCoverage93 [60,28] 28 5 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0093 : NodeCoverage93 [60,27] 27 6 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0094 : NodeCoverage93 [60,26] 26 7 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0095 : NodeCoverage93 [60,25] 25 8 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0096 : NodeCoverage93 [60,24] 24 9 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0097 : NodeCoverage93 [60,23] 23 10 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0098 : NodeCoverage93 [60,22] 22 11 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0099 : NodeCoverage93 [60,21] 21 12 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0100 : NodeCoverage93 [60,20] 20 13 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0101 : NodeCoverage93 [60,19] 19 14 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0102 : NodeCoverage93 [60,18] 18 15 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0103 : NodeCoverage93 [60,17] 17 16 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0104 : NodeCoverage93 [60,16] 16 17 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0105 : NodeCoverage93 [60,15] 15 18 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0106 : NodeCoverage93 [60,14] 14 19 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0107 : NodeCoverage93 [60,13] 13 20 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0108 : NodeCoverage93 [60,12] 12 21 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0109 : NodeCoverage93 [60,11] 11 22 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0110 : NodeCoverage93 [60,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0111 : NodeCoverage93 [60,10,10,9] 9 4 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0112 : NodeCoverage93 [60,10,10,8] 8 5 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0113 : NodeCoverage93 [60,10,10,7] 7 6 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0114 : NodeCoverage93 [60,10,10,6] 6 7 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0115 : NodeCoverage93 [60,10,10,5] 5 8 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0116 : NodeCoverage93 [60,10,10,3] 3 10 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0117 : NodeCoverage93 [60,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0110
    (ChildrenCoverage93.cons _ _ compact93_node_0111
    (ChildrenCoverage93.cons _ _ compact93_node_0112
    (ChildrenCoverage93.cons _ _ compact93_node_0113
    (ChildrenCoverage93.cons _ _ compact93_node_0114
    (ChildrenCoverage93.cons _ _ compact93_node_0115
    (ChildrenCoverage93.cons _ _ compact93_node_0116
    ChildrenCoverage93.nil)))))))

theorem compact93_node_0118 : NodeCoverage93 [60,10,9] 9 14 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0119 : NodeCoverage93 [60,10,8] 8 15 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0120 : NodeCoverage93 [60,10,7] 7 16 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0121 : NodeCoverage93 [60,10,6] 6 17 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0122 : NodeCoverage93 [60,10,5] 5 18 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0123 : NodeCoverage93 [60,10,3] 3 20 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0124 : NodeCoverage93 [60,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0117
    (ChildrenCoverage93.cons _ _ compact93_node_0118
    (ChildrenCoverage93.cons _ _ compact93_node_0119
    (ChildrenCoverage93.cons _ _ compact93_node_0120
    (ChildrenCoverage93.cons _ _ compact93_node_0121
    (ChildrenCoverage93.cons _ _ compact93_node_0122
    (ChildrenCoverage93.cons _ _ compact93_node_0123
    ChildrenCoverage93.nil)))))))

end Symconf93
