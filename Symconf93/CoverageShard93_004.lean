module
public import Symconf93.CoverageShard93_003

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0256 : NodeCoverage93 [48,16,14] 14 15 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0257 : NodeCoverage93 [48,16,13] 13 16 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0258 : NodeCoverage93 [48,16,12,12] 12 5 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0259 : NodeCoverage93 [48,16,12,11] 11 6 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0260 : NodeCoverage93 [48,16,12,10] 10 7 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0261 : NodeCoverage93 [48,16,12,9] 9 8 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0262 : NodeCoverage93 [48,16,12,8] 8 9 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0263 : NodeCoverage93 [48,16,12,7] 7 10 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0264 : NodeCoverage93 [48,16,12,6] 6 11 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0265 : NodeCoverage93 [48,16,12,5] 5 12 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0266 : NodeCoverage93 [48,16,12,3] 3 14 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0267 : NodeCoverage93 [48,16,12] 12 17 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0258
    (ChildrenCoverage93.cons _ _ compact93_node_0259
    (ChildrenCoverage93.cons _ _ compact93_node_0260
    (ChildrenCoverage93.cons _ _ compact93_node_0261
    (ChildrenCoverage93.cons _ _ compact93_node_0262
    (ChildrenCoverage93.cons _ _ compact93_node_0263
    (ChildrenCoverage93.cons _ _ compact93_node_0264
    (ChildrenCoverage93.cons _ _ compact93_node_0265
    (ChildrenCoverage93.cons _ _ compact93_node_0266
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0268 : NodeCoverage93 [48,16,11] 11 18 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0269 : NodeCoverage93 [48,16,10] 10 19 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0270 : NodeCoverage93 [48,16,9] 9 20 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0271 : NodeCoverage93 [48,16,8] 8 21 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0272 : NodeCoverage93 [48,16,7] 7 22 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0273 : NodeCoverage93 [48,16,6] 6 23 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0274 : NodeCoverage93 [48,16,5] 5 24 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0275 : NodeCoverage93 [48,16,3] 3 26 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0276 : NodeCoverage93 [48,16] 16 29 :=
  node_fork93 (B := [16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0254
    (ChildrenCoverage93.cons _ _ compact93_node_0255
    (ChildrenCoverage93.cons _ _ compact93_node_0256
    (ChildrenCoverage93.cons _ _ compact93_node_0257
    (ChildrenCoverage93.cons _ _ compact93_node_0267
    (ChildrenCoverage93.cons _ _ compact93_node_0268
    (ChildrenCoverage93.cons _ _ compact93_node_0269
    (ChildrenCoverage93.cons _ _ compact93_node_0270
    (ChildrenCoverage93.cons _ _ compact93_node_0271
    (ChildrenCoverage93.cons _ _ compact93_node_0272
    (ChildrenCoverage93.cons _ _ compact93_node_0273
    (ChildrenCoverage93.cons _ _ compact93_node_0274
    (ChildrenCoverage93.cons _ _ compact93_node_0275
    ChildrenCoverage93.nil)))))))))))))

theorem compact93_node_0277 : NodeCoverage93 [48,15] 15 30 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0278 : NodeCoverage93 [48,14] 14 31 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0279 : NodeCoverage93 [48,13] 13 32 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0280 : NodeCoverage93 [48,12,12,12] 12 9 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0281 : NodeCoverage93 [48,12,12,11] 11 10 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0282 : NodeCoverage93 [48,12,12,10] 10 11 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0283 : NodeCoverage93 [48,12,12,9] 9 12 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0284 : NodeCoverage93 [48,12,12,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0285 : NodeCoverage93 [48,12,12,7] 7 14 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0286 : NodeCoverage93 [48,12,12,6] 6 15 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0287 : NodeCoverage93 [48,12,12,5] 5 16 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0288 : NodeCoverage93 [48,12,12,3] 3 18 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0289 : NodeCoverage93 [48,12,12] 12 21 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0280
    (ChildrenCoverage93.cons _ _ compact93_node_0281
    (ChildrenCoverage93.cons _ _ compact93_node_0282
    (ChildrenCoverage93.cons _ _ compact93_node_0283
    (ChildrenCoverage93.cons _ _ compact93_node_0284
    (ChildrenCoverage93.cons _ _ compact93_node_0285
    (ChildrenCoverage93.cons _ _ compact93_node_0286
    (ChildrenCoverage93.cons _ _ compact93_node_0287
    (ChildrenCoverage93.cons _ _ compact93_node_0288
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0290 : NodeCoverage93 [48,12,11] 11 22 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0291 : NodeCoverage93 [48,12,10] 10 23 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0292 : NodeCoverage93 [48,12,9] 9 24 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0293 : NodeCoverage93 [48,12,8] 8 25 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0294 : NodeCoverage93 [48,12,7] 7 26 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0295 : NodeCoverage93 [48,12,6] 6 27 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0296 : NodeCoverage93 [48,12,5] 5 28 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0297 : NodeCoverage93 [48,12,3] 3 30 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0298 : NodeCoverage93 [48,12] 12 33 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0289
    (ChildrenCoverage93.cons _ _ compact93_node_0290
    (ChildrenCoverage93.cons _ _ compact93_node_0291
    (ChildrenCoverage93.cons _ _ compact93_node_0292
    (ChildrenCoverage93.cons _ _ compact93_node_0293
    (ChildrenCoverage93.cons _ _ compact93_node_0294
    (ChildrenCoverage93.cons _ _ compact93_node_0295
    (ChildrenCoverage93.cons _ _ compact93_node_0296
    (ChildrenCoverage93.cons _ _ compact93_node_0297
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0299 : NodeCoverage93 [48,11] 11 34 :=
  demand_node_prune93 48 compact93_demands_48 compact93_demands_48_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
