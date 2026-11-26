module
public import Symconf93.CoverageShard93_005

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0353 : NodeCoverage93 [45,15,15] 15 18 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0341
    (ChildrenCoverage93.cons _ _ compact93_node_0342
    (ChildrenCoverage93.cons _ _ compact93_node_0343
    (ChildrenCoverage93.cons _ _ compact93_node_0344
    (ChildrenCoverage93.cons _ _ compact93_node_0345
    (ChildrenCoverage93.cons _ _ compact93_node_0346
    (ChildrenCoverage93.cons _ _ compact93_node_0347
    (ChildrenCoverage93.cons _ _ compact93_node_0348
    (ChildrenCoverage93.cons _ _ compact93_node_0349
    (ChildrenCoverage93.cons _ _ compact93_node_0350
    (ChildrenCoverage93.cons _ _ compact93_node_0351
    (ChildrenCoverage93.cons _ _ compact93_node_0352
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_0354 : NodeCoverage93 [45,15,14] 14 19 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0355 : NodeCoverage93 [45,15,13] 13 20 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0356 : NodeCoverage93 [45,15,12] 12 21 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0357 : NodeCoverage93 [45,15,11] 11 22 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0358 : NodeCoverage93 [45,15,10] 10 23 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0359 : NodeCoverage93 [45,15,9,9,9] 9 6 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0360 : NodeCoverage93 [45,15,9,9,8] 8 7 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0361 : NodeCoverage93 [45,15,9,9,7] 7 8 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0362 : NodeCoverage93 [45,15,9,9,6] 6 9 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0363 : NodeCoverage93 [45,15,9,9,5] 5 10 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0364 : NodeCoverage93 [45,15,9,9,3] 3 12 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0365 : NodeCoverage93 [45,15,9,9] 9 15 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0359
    (ChildrenCoverage93.cons _ _ compact93_node_0360
    (ChildrenCoverage93.cons _ _ compact93_node_0361
    (ChildrenCoverage93.cons _ _ compact93_node_0362
    (ChildrenCoverage93.cons _ _ compact93_node_0363
    (ChildrenCoverage93.cons _ _ compact93_node_0364
    ChildrenCoverage93.nil))))))

theorem compact93_node_0366 : NodeCoverage93 [45,15,9,8] 8 16 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0367 : NodeCoverage93 [45,15,9,7] 7 17 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0368 : NodeCoverage93 [45,15,9,6] 6 18 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0369 : NodeCoverage93 [45,15,9,5] 5 19 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0370 : NodeCoverage93 [45,15,9,3] 3 21 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0371 : NodeCoverage93 [45,15,9] 9 24 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0365
    (ChildrenCoverage93.cons _ _ compact93_node_0366
    (ChildrenCoverage93.cons _ _ compact93_node_0367
    (ChildrenCoverage93.cons _ _ compact93_node_0368
    (ChildrenCoverage93.cons _ _ compact93_node_0369
    (ChildrenCoverage93.cons _ _ compact93_node_0370
    ChildrenCoverage93.nil))))))

theorem compact93_node_0372 : NodeCoverage93 [45,15,8] 8 25 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0373 : NodeCoverage93 [45,15,7] 7 26 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0374 : NodeCoverage93 [45,15,6] 6 27 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0375 : NodeCoverage93 [45,15,5] 5 28 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0376 : NodeCoverage93 [45,15,3] 3 30 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0377 : NodeCoverage93 [45,15] 15 33 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0353
    (ChildrenCoverage93.cons _ _ compact93_node_0354
    (ChildrenCoverage93.cons _ _ compact93_node_0355
    (ChildrenCoverage93.cons _ _ compact93_node_0356
    (ChildrenCoverage93.cons _ _ compact93_node_0357
    (ChildrenCoverage93.cons _ _ compact93_node_0358
    (ChildrenCoverage93.cons _ _ compact93_node_0371
    (ChildrenCoverage93.cons _ _ compact93_node_0372
    (ChildrenCoverage93.cons _ _ compact93_node_0373
    (ChildrenCoverage93.cons _ _ compact93_node_0374
    (ChildrenCoverage93.cons _ _ compact93_node_0375
    (ChildrenCoverage93.cons _ _ compact93_node_0376
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_0378 : NodeCoverage93 [45,14] 14 34 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0379 : NodeCoverage93 [45,13] 13 35 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0380 : NodeCoverage93 [45,12] 12 36 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0381 : NodeCoverage93 [45,11] 11 37 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0382 : NodeCoverage93 [45,10] 10 38 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0383 : NodeCoverage93 [45,9] 9 39 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0384 : NodeCoverage93 [45,8] 8 40 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0385 : NodeCoverage93 [45,7] 7 41 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0386 : NodeCoverage93 [45,6] 6 42 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0387 : NodeCoverage93 [45,5] 5 43 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0388 : NodeCoverage93 [45,3] 3 45 :=
  demand_node_prune93 45 compact93_demands_45 compact93_demands_45_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0389 : NodeCoverage93 [45] 45 48 :=
  node_fork93 (B := [45,44,43,42,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0311
    (ChildrenCoverage93.cons _ _ compact93_node_0312
    (ChildrenCoverage93.cons _ _ compact93_node_0313
    (ChildrenCoverage93.cons _ _ compact93_node_0314
    (ChildrenCoverage93.cons _ _ compact93_node_0315
    (ChildrenCoverage93.cons _ _ compact93_node_0316
    (ChildrenCoverage93.cons _ _ compact93_node_0317
    (ChildrenCoverage93.cons _ _ compact93_node_0318
    (ChildrenCoverage93.cons _ _ compact93_node_0319
    (ChildrenCoverage93.cons _ _ compact93_node_0320
    (ChildrenCoverage93.cons _ _ compact93_node_0321
    (ChildrenCoverage93.cons _ _ compact93_node_0322
    (ChildrenCoverage93.cons _ _ compact93_node_0323
    (ChildrenCoverage93.cons _ _ compact93_node_0324
    (ChildrenCoverage93.cons _ _ compact93_node_0325
    (ChildrenCoverage93.cons _ _ compact93_node_0326
    (ChildrenCoverage93.cons _ _ compact93_node_0327
    (ChildrenCoverage93.cons _ _ compact93_node_0328
    (ChildrenCoverage93.cons _ _ compact93_node_0329
    (ChildrenCoverage93.cons _ _ compact93_node_0330
    (ChildrenCoverage93.cons _ _ compact93_node_0331
    (ChildrenCoverage93.cons _ _ compact93_node_0332
    (ChildrenCoverage93.cons _ _ compact93_node_0333
    (ChildrenCoverage93.cons _ _ compact93_node_0334
    (ChildrenCoverage93.cons _ _ compact93_node_0335
    (ChildrenCoverage93.cons _ _ compact93_node_0336
    (ChildrenCoverage93.cons _ _ compact93_node_0337
    (ChildrenCoverage93.cons _ _ compact93_node_0338
    (ChildrenCoverage93.cons _ _ compact93_node_0339
    (ChildrenCoverage93.cons _ _ compact93_node_0340
    (ChildrenCoverage93.cons _ _ compact93_node_0377
    (ChildrenCoverage93.cons _ _ compact93_node_0378
    (ChildrenCoverage93.cons _ _ compact93_node_0379
    (ChildrenCoverage93.cons _ _ compact93_node_0380
    (ChildrenCoverage93.cons _ _ compact93_node_0381
    (ChildrenCoverage93.cons _ _ compact93_node_0382
    (ChildrenCoverage93.cons _ _ compact93_node_0383
    (ChildrenCoverage93.cons _ _ compact93_node_0384
    (ChildrenCoverage93.cons _ _ compact93_node_0385
    (ChildrenCoverage93.cons _ _ compact93_node_0386
    (ChildrenCoverage93.cons _ _ compact93_node_0387
    (ChildrenCoverage93.cons _ _ compact93_node_0388
    ChildrenCoverage93.nil))))))))))))))))))))))))))))))))))))))))))

theorem compact93_node_0390 : NodeCoverage93 [44] 44 49 :=
  demand_node_prune93 44 compact93_demands_44 compact93_demands_44_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0391 : NodeCoverage93 [43,43,7] 7 0 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0392 : NodeCoverage93 [43,43,3] 3 4 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0393 : NodeCoverage93 [43,43] 43 7 :=
  node_fork93 (B := [7,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0391
    (ChildrenCoverage93.cons _ _ compact93_node_0392
    ChildrenCoverage93.nil))

theorem compact93_node_0394 : NodeCoverage93 [43,42] 42 8 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0395 : NodeCoverage93 [43,41] 41 9 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0396 : NodeCoverage93 [43,40] 40 10 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0397 : NodeCoverage93 [43,39] 39 11 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0398 : NodeCoverage93 [43,38] 38 12 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0399 : NodeCoverage93 [43,37] 37 13 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0400 : NodeCoverage93 [43,36] 36 14 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0401 : NodeCoverage93 [43,35] 35 15 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0402 : NodeCoverage93 [43,34] 34 16 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0403 : NodeCoverage93 [43,33] 33 17 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0404 : NodeCoverage93 [43,32] 32 18 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0405 : NodeCoverage93 [43,31] 31 19 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0406 : NodeCoverage93 [43,30] 30 20 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0407 : NodeCoverage93 [43,29] 29 21 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0408 : NodeCoverage93 [43,28] 28 22 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0409 : NodeCoverage93 [43,27] 27 23 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0410 : NodeCoverage93 [43,26] 26 24 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0411 : NodeCoverage93 [43,25] 25 25 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0412 : NodeCoverage93 [43,24] 24 26 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0413 : NodeCoverage93 [43,23] 23 27 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0414 : NodeCoverage93 [43,22] 22 28 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0415 : NodeCoverage93 [43,21] 21 29 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0416 : NodeCoverage93 [43,20] 20 30 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0417 : NodeCoverage93 [43,19] 19 31 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0418 : NodeCoverage93 [43,18] 18 32 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0419 : NodeCoverage93 [43,17] 17 33 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0420 : NodeCoverage93 [43,16] 16 34 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0421 : NodeCoverage93 [43,15] 15 35 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0422 : NodeCoverage93 [43,14] 14 36 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0423 : NodeCoverage93 [43,13] 13 37 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0424 : NodeCoverage93 [43,12] 12 38 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0425 : NodeCoverage93 [43,11] 11 39 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0426 : NodeCoverage93 [43,10] 10 40 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0427 : NodeCoverage93 [43,9] 9 41 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
