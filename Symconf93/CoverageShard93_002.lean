module
public import Symconf93.CoverageShard93_001

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0125 : NodeCoverage93 [60,9] 9 24 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0126 : NodeCoverage93 [60,8] 8 25 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0127 : NodeCoverage93 [60,7] 7 26 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0128 : NodeCoverage93 [60,6] 6 27 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0129 : NodeCoverage93 [60,5] 5 28 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0130 : NodeCoverage93 [60,3] 3 30 :=
  demand_node_prune93 60 compact93_demands_60 compact93_demands_60_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0131 : NodeCoverage93 [60] 60 33 :=
  node_fork93 (B := [33,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0089
    (ChildrenCoverage93.cons _ _ compact93_node_0090
    (ChildrenCoverage93.cons _ _ compact93_node_0091
    (ChildrenCoverage93.cons _ _ compact93_node_0092
    (ChildrenCoverage93.cons _ _ compact93_node_0093
    (ChildrenCoverage93.cons _ _ compact93_node_0094
    (ChildrenCoverage93.cons _ _ compact93_node_0095
    (ChildrenCoverage93.cons _ _ compact93_node_0096
    (ChildrenCoverage93.cons _ _ compact93_node_0097
    (ChildrenCoverage93.cons _ _ compact93_node_0098
    (ChildrenCoverage93.cons _ _ compact93_node_0099
    (ChildrenCoverage93.cons _ _ compact93_node_0100
    (ChildrenCoverage93.cons _ _ compact93_node_0101
    (ChildrenCoverage93.cons _ _ compact93_node_0102
    (ChildrenCoverage93.cons _ _ compact93_node_0103
    (ChildrenCoverage93.cons _ _ compact93_node_0104
    (ChildrenCoverage93.cons _ _ compact93_node_0105
    (ChildrenCoverage93.cons _ _ compact93_node_0106
    (ChildrenCoverage93.cons _ _ compact93_node_0107
    (ChildrenCoverage93.cons _ _ compact93_node_0108
    (ChildrenCoverage93.cons _ _ compact93_node_0109
    (ChildrenCoverage93.cons _ _ compact93_node_0124
    (ChildrenCoverage93.cons _ _ compact93_node_0125
    (ChildrenCoverage93.cons _ _ compact93_node_0126
    (ChildrenCoverage93.cons _ _ compact93_node_0127
    (ChildrenCoverage93.cons _ _ compact93_node_0128
    (ChildrenCoverage93.cons _ _ compact93_node_0129
    (ChildrenCoverage93.cons _ _ compact93_node_0130
    ChildrenCoverage93.nil))))))))))))))))))))))))))))

theorem compact93_node_0132 : NodeCoverage93 [59] 59 34 :=
  demand_node_prune93 59 compact93_demands_59 compact93_demands_59_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0133 : NodeCoverage93 [58] 58 35 :=
  demand_node_prune93 58 compact93_demands_58 compact93_demands_58_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0134 : NodeCoverage93 [57] 57 36 :=
  demand_node_prune93 57 compact93_demands_57 compact93_demands_57_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0135 : NodeCoverage93 [56,37] 37 0 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0136 : NodeCoverage93 [56,34] 34 3 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0137 : NodeCoverage93 [56,33] 33 4 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0138 : NodeCoverage93 [56,32] 32 5 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0139 : NodeCoverage93 [56,31] 31 6 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0140 : NodeCoverage93 [56,30] 30 7 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0141 : NodeCoverage93 [56,29] 29 8 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0142 : NodeCoverage93 [56,28] 28 9 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0143 : NodeCoverage93 [56,27] 27 10 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0144 : NodeCoverage93 [56,26] 26 11 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0145 : NodeCoverage93 [56,25] 25 12 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0146 : NodeCoverage93 [56,24] 24 13 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0147 : NodeCoverage93 [56,23] 23 14 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0148 : NodeCoverage93 [56,22] 22 15 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0149 : NodeCoverage93 [56,21] 21 16 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0150 : NodeCoverage93 [56,20] 20 17 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0151 : NodeCoverage93 [56,19] 19 18 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0152 : NodeCoverage93 [56,18] 18 19 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0153 : NodeCoverage93 [56,17] 17 20 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0154 : NodeCoverage93 [56,16] 16 21 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0155 : NodeCoverage93 [56,15] 15 22 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0156 : NodeCoverage93 [56,14] 14 23 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0157 : NodeCoverage93 [56,13] 13 24 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0158 : NodeCoverage93 [56,12] 12 25 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0159 : NodeCoverage93 [56,11] 11 26 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0160 : NodeCoverage93 [56,10] 10 27 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0161 : NodeCoverage93 [56,9] 9 28 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0162 : NodeCoverage93 [56,8] 8 29 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0163 : NodeCoverage93 [56,7] 7 30 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0164 : NodeCoverage93 [56,6] 6 31 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0165 : NodeCoverage93 [56,5] 5 32 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0166 : NodeCoverage93 [56,3] 3 34 :=
  demand_node_prune93 56 compact93_demands_56 compact93_demands_56_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0167 : NodeCoverage93 [56] 56 37 :=
  node_fork93 (B := [37,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0135
    (ChildrenCoverage93.cons _ _ compact93_node_0136
    (ChildrenCoverage93.cons _ _ compact93_node_0137
    (ChildrenCoverage93.cons _ _ compact93_node_0138
    (ChildrenCoverage93.cons _ _ compact93_node_0139
    (ChildrenCoverage93.cons _ _ compact93_node_0140
    (ChildrenCoverage93.cons _ _ compact93_node_0141
    (ChildrenCoverage93.cons _ _ compact93_node_0142
    (ChildrenCoverage93.cons _ _ compact93_node_0143
    (ChildrenCoverage93.cons _ _ compact93_node_0144
    (ChildrenCoverage93.cons _ _ compact93_node_0145
    (ChildrenCoverage93.cons _ _ compact93_node_0146
    (ChildrenCoverage93.cons _ _ compact93_node_0147
    (ChildrenCoverage93.cons _ _ compact93_node_0148
    (ChildrenCoverage93.cons _ _ compact93_node_0149
    (ChildrenCoverage93.cons _ _ compact93_node_0150
    (ChildrenCoverage93.cons _ _ compact93_node_0151
    (ChildrenCoverage93.cons _ _ compact93_node_0152
    (ChildrenCoverage93.cons _ _ compact93_node_0153
    (ChildrenCoverage93.cons _ _ compact93_node_0154
    (ChildrenCoverage93.cons _ _ compact93_node_0155
    (ChildrenCoverage93.cons _ _ compact93_node_0156
    (ChildrenCoverage93.cons _ _ compact93_node_0157
    (ChildrenCoverage93.cons _ _ compact93_node_0158
    (ChildrenCoverage93.cons _ _ compact93_node_0159
    (ChildrenCoverage93.cons _ _ compact93_node_0160
    (ChildrenCoverage93.cons _ _ compact93_node_0161
    (ChildrenCoverage93.cons _ _ compact93_node_0162
    (ChildrenCoverage93.cons _ _ compact93_node_0163
    (ChildrenCoverage93.cons _ _ compact93_node_0164
    (ChildrenCoverage93.cons _ _ compact93_node_0165
    (ChildrenCoverage93.cons _ _ compact93_node_0166
    ChildrenCoverage93.nil))))))))))))))))))))))))))))))))

theorem compact93_node_0168 : NodeCoverage93 [55] 55 38 :=
  demand_node_prune93 55 compact93_demands_55 compact93_demands_55_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0169 : NodeCoverage93 [54,39] 39 0 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0170 : NodeCoverage93 [54,36] 36 3 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0171 : NodeCoverage93 [54,35] 35 4 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0172 : NodeCoverage93 [54,34] 34 5 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0173 : NodeCoverage93 [54,33] 33 6 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0174 : NodeCoverage93 [54,32] 32 7 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0175 : NodeCoverage93 [54,31] 31 8 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0176 : NodeCoverage93 [54,30] 30 9 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0177 : NodeCoverage93 [54,29] 29 10 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0178 : NodeCoverage93 [54,28] 28 11 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0179 : NodeCoverage93 [54,27] 27 12 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0180 : NodeCoverage93 [54,26] 26 13 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0181 : NodeCoverage93 [54,25] 25 14 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0182 : NodeCoverage93 [54,24] 24 15 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0183 : NodeCoverage93 [54,23] 23 16 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0184 : NodeCoverage93 [54,22] 22 17 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0185 : NodeCoverage93 [54,21] 21 18 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0186 : NodeCoverage93 [54,20] 20 19 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0187 : NodeCoverage93 [54,19] 19 20 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0188 : NodeCoverage93 [54,18] 18 21 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0189 : NodeCoverage93 [54,17] 17 22 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0190 : NodeCoverage93 [54,16] 16 23 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0191 : NodeCoverage93 [54,15] 15 24 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0192 : NodeCoverage93 [54,14] 14 25 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0193 : NodeCoverage93 [54,13] 13 26 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0194 : NodeCoverage93 [54,12] 12 27 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0195 : NodeCoverage93 [54,11] 11 28 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0196 : NodeCoverage93 [54,10] 10 29 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0197 : NodeCoverage93 [54,9,9,9,9] 9 3 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0198 : NodeCoverage93 [54,9,9,9,8] 8 4 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0199 : NodeCoverage93 [54,9,9,9,7] 7 5 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
