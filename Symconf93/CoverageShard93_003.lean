module
public import Symconf93.CoverageShard93_002

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0200 : NodeCoverage93 [54,9,9,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0201 : NodeCoverage93 [54,9,9,9,5] 5 7 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0202 : NodeCoverage93 [54,9,9,9,3] 3 9 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0203 : NodeCoverage93 [54,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0197
    (ChildrenCoverage93.cons _ _ compact93_node_0198
    (ChildrenCoverage93.cons _ _ compact93_node_0199
    (ChildrenCoverage93.cons _ _ compact93_node_0200
    (ChildrenCoverage93.cons _ _ compact93_node_0201
    (ChildrenCoverage93.cons _ _ compact93_node_0202
    ChildrenCoverage93.nil))))))

theorem compact93_node_0204 : NodeCoverage93 [54,9,9,8] 8 13 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0205 : NodeCoverage93 [54,9,9,7] 7 14 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0206 : NodeCoverage93 [54,9,9,6] 6 15 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0207 : NodeCoverage93 [54,9,9,5] 5 16 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0208 : NodeCoverage93 [54,9,9,3] 3 18 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0209 : NodeCoverage93 [54,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0203
    (ChildrenCoverage93.cons _ _ compact93_node_0204
    (ChildrenCoverage93.cons _ _ compact93_node_0205
    (ChildrenCoverage93.cons _ _ compact93_node_0206
    (ChildrenCoverage93.cons _ _ compact93_node_0207
    (ChildrenCoverage93.cons _ _ compact93_node_0208
    ChildrenCoverage93.nil))))))

theorem compact93_node_0210 : NodeCoverage93 [54,9,8] 8 22 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0211 : NodeCoverage93 [54,9,7] 7 23 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0212 : NodeCoverage93 [54,9,6] 6 24 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0213 : NodeCoverage93 [54,9,5] 5 25 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0214 : NodeCoverage93 [54,9,3] 3 27 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0215 : NodeCoverage93 [54,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0209
    (ChildrenCoverage93.cons _ _ compact93_node_0210
    (ChildrenCoverage93.cons _ _ compact93_node_0211
    (ChildrenCoverage93.cons _ _ compact93_node_0212
    (ChildrenCoverage93.cons _ _ compact93_node_0213
    (ChildrenCoverage93.cons _ _ compact93_node_0214
    ChildrenCoverage93.nil))))))

theorem compact93_node_0216 : NodeCoverage93 [54,8] 8 31 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0217 : NodeCoverage93 [54,7] 7 32 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0218 : NodeCoverage93 [54,6] 6 33 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0219 : NodeCoverage93 [54,5] 5 34 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0220 : NodeCoverage93 [54,3] 3 36 :=
  demand_node_prune93 54 compact93_demands_54 compact93_demands_54_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0221 : NodeCoverage93 [54] 54 39 :=
  node_fork93 (B := [39,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0169
    (ChildrenCoverage93.cons _ _ compact93_node_0170
    (ChildrenCoverage93.cons _ _ compact93_node_0171
    (ChildrenCoverage93.cons _ _ compact93_node_0172
    (ChildrenCoverage93.cons _ _ compact93_node_0173
    (ChildrenCoverage93.cons _ _ compact93_node_0174
    (ChildrenCoverage93.cons _ _ compact93_node_0175
    (ChildrenCoverage93.cons _ _ compact93_node_0176
    (ChildrenCoverage93.cons _ _ compact93_node_0177
    (ChildrenCoverage93.cons _ _ compact93_node_0178
    (ChildrenCoverage93.cons _ _ compact93_node_0179
    (ChildrenCoverage93.cons _ _ compact93_node_0180
    (ChildrenCoverage93.cons _ _ compact93_node_0181
    (ChildrenCoverage93.cons _ _ compact93_node_0182
    (ChildrenCoverage93.cons _ _ compact93_node_0183
    (ChildrenCoverage93.cons _ _ compact93_node_0184
    (ChildrenCoverage93.cons _ _ compact93_node_0185
    (ChildrenCoverage93.cons _ _ compact93_node_0186
    (ChildrenCoverage93.cons _ _ compact93_node_0187
    (ChildrenCoverage93.cons _ _ compact93_node_0188
    (ChildrenCoverage93.cons _ _ compact93_node_0189
    (ChildrenCoverage93.cons _ _ compact93_node_0190
    (ChildrenCoverage93.cons _ _ compact93_node_0191
    (ChildrenCoverage93.cons _ _ compact93_node_0192
    (ChildrenCoverage93.cons _ _ compact93_node_0193
    (ChildrenCoverage93.cons _ _ compact93_node_0194
    (ChildrenCoverage93.cons _ _ compact93_node_0195
    (ChildrenCoverage93.cons _ _ compact93_node_0196
    (ChildrenCoverage93.cons _ _ compact93_node_0215
    (ChildrenCoverage93.cons _ _ compact93_node_0216
    (ChildrenCoverage93.cons _ _ compact93_node_0217
    (ChildrenCoverage93.cons _ _ compact93_node_0218
    (ChildrenCoverage93.cons _ _ compact93_node_0219
    (ChildrenCoverage93.cons _ _ compact93_node_0220
    ChildrenCoverage93.nil))))))))))))))))))))))))))))))))))

theorem compact93_node_0222 : NodeCoverage93 [53] 53 40 :=
  demand_node_prune93 53 compact93_demands_53 compact93_demands_53_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0223 : NodeCoverage93 [52] 52 41 :=
  demand_node_prune93 52 compact93_demands_52 compact93_demands_52_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0224 : NodeCoverage93 [51] 51 42 :=
  demand_node_prune93 51 compact93_demands_51 compact93_demands_51_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0225 : NodeCoverage93 [50] 50 43 :=
  demand_node_prune93 50 compact93_demands_50 compact93_demands_50_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0226 : NodeCoverage93 [49] 49 44 :=
  demand_node_prune93 49 compact93_demands_49 compact93_demands_49_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0227 : NodeCoverage93 [48,45] 45 0 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0228 : NodeCoverage93 [48,42] 42 3 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0229 : NodeCoverage93 [48,41] 41 4 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0230 : NodeCoverage93 [48,40] 40 5 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0231 : NodeCoverage93 [48,39] 39 6 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0232 : NodeCoverage93 [48,38] 38 7 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0233 : NodeCoverage93 [48,37] 37 8 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0234 : NodeCoverage93 [48,36] 36 9 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0235 : NodeCoverage93 [48,35] 35 10 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0236 : NodeCoverage93 [48,34] 34 11 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0237 : NodeCoverage93 [48,33] 33 12 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0238 : NodeCoverage93 [48,32] 32 13 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0239 : NodeCoverage93 [48,31] 31 14 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0240 : NodeCoverage93 [48,30] 30 15 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0241 : NodeCoverage93 [48,29] 29 16 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0242 : NodeCoverage93 [48,28] 28 17 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0243 : NodeCoverage93 [48,27] 27 18 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0244 : NodeCoverage93 [48,26] 26 19 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0245 : NodeCoverage93 [48,25] 25 20 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0246 : NodeCoverage93 [48,24] 24 21 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0247 : NodeCoverage93 [48,23] 23 22 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0248 : NodeCoverage93 [48,22] 22 23 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0249 : NodeCoverage93 [48,21] 21 24 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0250 : NodeCoverage93 [48,20] 20 25 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0251 : NodeCoverage93 [48,19] 19 26 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0252 : NodeCoverage93 [48,18] 18 27 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0253 : NodeCoverage93 [48,17] 17 28 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0254 : NodeCoverage93 [48,16,16] 16 13 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0255 : NodeCoverage93 [48,16,15] 15 14 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
