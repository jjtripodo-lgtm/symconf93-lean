module
public import Symconf93.CoverageShard93_004

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0300 : NodeCoverage93 [48,10] 10 35 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0301 : NodeCoverage93 [48,9] 9 36 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0302 : NodeCoverage93 [48,8] 8 37 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0303 : NodeCoverage93 [48,7] 7 38 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0304 : NodeCoverage93 [48,6] 6 39 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0305 : NodeCoverage93 [48,5] 5 40 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0306 : NodeCoverage93 [48,3] 3 42 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0307 : NodeCoverage93 [48] 48 45 :=
  node_fork93 (B := [45,42,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0227
    (ChildrenCoverage93.cons _ _ compact93_node_0228
    (ChildrenCoverage93.cons _ _ compact93_node_0229
    (ChildrenCoverage93.cons _ _ compact93_node_0230
    (ChildrenCoverage93.cons _ _ compact93_node_0231
    (ChildrenCoverage93.cons _ _ compact93_node_0232
    (ChildrenCoverage93.cons _ _ compact93_node_0233
    (ChildrenCoverage93.cons _ _ compact93_node_0234
    (ChildrenCoverage93.cons _ _ compact93_node_0235
    (ChildrenCoverage93.cons _ _ compact93_node_0236
    (ChildrenCoverage93.cons _ _ compact93_node_0237
    (ChildrenCoverage93.cons _ _ compact93_node_0238
    (ChildrenCoverage93.cons _ _ compact93_node_0239
    (ChildrenCoverage93.cons _ _ compact93_node_0240
    (ChildrenCoverage93.cons _ _ compact93_node_0241
    (ChildrenCoverage93.cons _ _ compact93_node_0242
    (ChildrenCoverage93.cons _ _ compact93_node_0243
    (ChildrenCoverage93.cons _ _ compact93_node_0244
    (ChildrenCoverage93.cons _ _ compact93_node_0245
    (ChildrenCoverage93.cons _ _ compact93_node_0246
    (ChildrenCoverage93.cons _ _ compact93_node_0247
    (ChildrenCoverage93.cons _ _ compact93_node_0248
    (ChildrenCoverage93.cons _ _ compact93_node_0249
    (ChildrenCoverage93.cons _ _ compact93_node_0250
    (ChildrenCoverage93.cons _ _ compact93_node_0251
    (ChildrenCoverage93.cons _ _ compact93_node_0252
    (ChildrenCoverage93.cons _ _ compact93_node_0253
    (ChildrenCoverage93.cons _ _ compact93_node_0276
    (ChildrenCoverage93.cons _ _ compact93_node_0277
    (ChildrenCoverage93.cons _ _ compact93_node_0278
    (ChildrenCoverage93.cons _ _ compact93_node_0279
    (ChildrenCoverage93.cons _ _ compact93_node_0298
    (ChildrenCoverage93.cons _ _ compact93_node_0299
    (ChildrenCoverage93.cons _ _ compact93_node_0300
    (ChildrenCoverage93.cons _ _ compact93_node_0301
    (ChildrenCoverage93.cons _ _ compact93_node_0302
    (ChildrenCoverage93.cons _ _ compact93_node_0303
    (ChildrenCoverage93.cons _ _ compact93_node_0304
    (ChildrenCoverage93.cons _ _ compact93_node_0305
    (ChildrenCoverage93.cons _ _ compact93_node_0306
    ChildrenCoverage93.nil))))))))))))))))))))))))))))))))))))))))

theorem compact93_node_0308 : NodeCoverage93 [47] 47 46 :=
  demand_node_prune93 47 compact93_demands_47 compact93_demands_47_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0309 : NodeCoverage93 [46] 46 47 :=
  demand_node_prune93 46 compact93_demands_46 compact93_demands_46_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0310 : NodeCoverage93 [45,45,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0311 : NodeCoverage93 [45,45] 45 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0310
    ChildrenCoverage93.nil)

theorem compact93_node_0312 : NodeCoverage93 [45,44] 44 4 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0313 : NodeCoverage93 [45,43] 43 5 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0314 : NodeCoverage93 [45,42] 42 6 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0315 : NodeCoverage93 [45,41] 41 7 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0316 : NodeCoverage93 [45,40] 40 8 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0317 : NodeCoverage93 [45,39] 39 9 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0318 : NodeCoverage93 [45,38] 38 10 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0319 : NodeCoverage93 [45,37] 37 11 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0320 : NodeCoverage93 [45,36] 36 12 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0321 : NodeCoverage93 [45,35] 35 13 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0322 : NodeCoverage93 [45,34] 34 14 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0323 : NodeCoverage93 [45,33] 33 15 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0324 : NodeCoverage93 [45,32] 32 16 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0325 : NodeCoverage93 [45,31] 31 17 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0326 : NodeCoverage93 [45,30] 30 18 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0327 : NodeCoverage93 [45,29] 29 19 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0328 : NodeCoverage93 [45,28] 28 20 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0329 : NodeCoverage93 [45,27] 27 21 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0330 : NodeCoverage93 [45,26] 26 22 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0331 : NodeCoverage93 [45,25] 25 23 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0332 : NodeCoverage93 [45,24] 24 24 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0333 : NodeCoverage93 [45,23] 23 25 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0334 : NodeCoverage93 [45,22] 22 26 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0335 : NodeCoverage93 [45,21] 21 27 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0336 : NodeCoverage93 [45,20] 20 28 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0337 : NodeCoverage93 [45,19] 19 29 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0338 : NodeCoverage93 [45,18] 18 30 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0339 : NodeCoverage93 [45,17] 17 31 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0340 : NodeCoverage93 [45,16] 16 32 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0341 : NodeCoverage93 [45,15,15,15] 15 3 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0342 : NodeCoverage93 [45,15,15,14] 14 4 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0343 : NodeCoverage93 [45,15,15,13] 13 5 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0344 : NodeCoverage93 [45,15,15,12] 12 6 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0345 : NodeCoverage93 [45,15,15,11] 11 7 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0346 : NodeCoverage93 [45,15,15,10] 10 8 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0347 : NodeCoverage93 [45,15,15,9] 9 9 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0348 : NodeCoverage93 [45,15,15,8] 8 10 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0349 : NodeCoverage93 [45,15,15,7] 7 11 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0350 : NodeCoverage93 [45,15,15,6] 6 12 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0351 : NodeCoverage93 [45,15,15,5] 5 13 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0352 : NodeCoverage93 [45,15,15,3] 3 15 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
