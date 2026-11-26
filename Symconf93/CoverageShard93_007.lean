module
public import Symconf93.CoverageShard93_006

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0428 : NodeCoverage93 [43,8] 8 42 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0429 : NodeCoverage93 [43,7] 7 43 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0430 : NodeCoverage93 [43,6] 6 44 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0431 : NodeCoverage93 [43,5] 5 45 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0432 : NodeCoverage93 [43,3] 3 47 :=
  demand_node_prune93 43 compact93_demands_43 compact93_demands_43_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0433 : NodeCoverage93 [43] 43 50 :=
  node_fork93 (B := [43,42,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0393
    (ChildrenCoverage93.cons _ _ compact93_node_0394
    (ChildrenCoverage93.cons _ _ compact93_node_0395
    (ChildrenCoverage93.cons _ _ compact93_node_0396
    (ChildrenCoverage93.cons _ _ compact93_node_0397
    (ChildrenCoverage93.cons _ _ compact93_node_0398
    (ChildrenCoverage93.cons _ _ compact93_node_0399
    (ChildrenCoverage93.cons _ _ compact93_node_0400
    (ChildrenCoverage93.cons _ _ compact93_node_0401
    (ChildrenCoverage93.cons _ _ compact93_node_0402
    (ChildrenCoverage93.cons _ _ compact93_node_0403
    (ChildrenCoverage93.cons _ _ compact93_node_0404
    (ChildrenCoverage93.cons _ _ compact93_node_0405
    (ChildrenCoverage93.cons _ _ compact93_node_0406
    (ChildrenCoverage93.cons _ _ compact93_node_0407
    (ChildrenCoverage93.cons _ _ compact93_node_0408
    (ChildrenCoverage93.cons _ _ compact93_node_0409
    (ChildrenCoverage93.cons _ _ compact93_node_0410
    (ChildrenCoverage93.cons _ _ compact93_node_0411
    (ChildrenCoverage93.cons _ _ compact93_node_0412
    (ChildrenCoverage93.cons _ _ compact93_node_0413
    (ChildrenCoverage93.cons _ _ compact93_node_0414
    (ChildrenCoverage93.cons _ _ compact93_node_0415
    (ChildrenCoverage93.cons _ _ compact93_node_0416
    (ChildrenCoverage93.cons _ _ compact93_node_0417
    (ChildrenCoverage93.cons _ _ compact93_node_0418
    (ChildrenCoverage93.cons _ _ compact93_node_0419
    (ChildrenCoverage93.cons _ _ compact93_node_0420
    (ChildrenCoverage93.cons _ _ compact93_node_0421
    (ChildrenCoverage93.cons _ _ compact93_node_0422
    (ChildrenCoverage93.cons _ _ compact93_node_0423
    (ChildrenCoverage93.cons _ _ compact93_node_0424
    (ChildrenCoverage93.cons _ _ compact93_node_0425
    (ChildrenCoverage93.cons _ _ compact93_node_0426
    (ChildrenCoverage93.cons _ _ compact93_node_0427
    (ChildrenCoverage93.cons _ _ compact93_node_0428
    (ChildrenCoverage93.cons _ _ compact93_node_0429
    (ChildrenCoverage93.cons _ _ compact93_node_0430
    (ChildrenCoverage93.cons _ _ compact93_node_0431
    (ChildrenCoverage93.cons _ _ compact93_node_0432
    ChildrenCoverage93.nil))))))))))))))))))))))))))))))))))))))))

theorem compact93_node_0434 : NodeCoverage93 [42,42] 42 9 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0435 : NodeCoverage93 [42,41] 41 10 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0436 : NodeCoverage93 [42,40] 40 11 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0437 : NodeCoverage93 [42,39] 39 12 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0438 : NodeCoverage93 [42,38] 38 13 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0439 : NodeCoverage93 [42,37] 37 14 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0440 : NodeCoverage93 [42,36] 36 15 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0441 : NodeCoverage93 [42,35] 35 16 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0442 : NodeCoverage93 [42,34] 34 17 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0443 : NodeCoverage93 [42,33] 33 18 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0444 : NodeCoverage93 [42,32] 32 19 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0445 : NodeCoverage93 [42,31] 31 20 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0446 : NodeCoverage93 [42,30] 30 21 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0447 : NodeCoverage93 [42,29] 29 22 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0448 : NodeCoverage93 [42,28] 28 23 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0449 : NodeCoverage93 [42,27] 27 24 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0450 : NodeCoverage93 [42,26] 26 25 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0451 : NodeCoverage93 [42,25] 25 26 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0452 : NodeCoverage93 [42,24] 24 27 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0453 : NodeCoverage93 [42,23] 23 28 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0454 : NodeCoverage93 [42,22] 22 29 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0455 : NodeCoverage93 [42,21] 21 30 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0456 : NodeCoverage93 [42,20] 20 31 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0457 : NodeCoverage93 [42,19] 19 32 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0458 : NodeCoverage93 [42,18] 18 33 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0459 : NodeCoverage93 [42,17] 17 34 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0460 : NodeCoverage93 [42,16] 16 35 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0461 : NodeCoverage93 [42,15] 15 36 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0462 : NodeCoverage93 [42,14] 14 37 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0463 : NodeCoverage93 [42,13] 13 38 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0464 : NodeCoverage93 [42,12] 12 39 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0465 : NodeCoverage93 [42,11] 11 40 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0466 : NodeCoverage93 [42,10] 10 41 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0467 : NodeCoverage93 [42,9] 9 42 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0468 : NodeCoverage93 [42,8] 8 43 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0469 : NodeCoverage93 [42,7] 7 44 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0470 : NodeCoverage93 [42,6] 6 45 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0471 : NodeCoverage93 [42,5] 5 46 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0472 : NodeCoverage93 [42,3] 3 48 :=
  demand_node_prune93 42 compact93_demands_42 compact93_demands_42_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0473 : NodeCoverage93 [42] 42 51 :=
  node_fork93 (B := [42,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0434
    (ChildrenCoverage93.cons _ _ compact93_node_0435
    (ChildrenCoverage93.cons _ _ compact93_node_0436
    (ChildrenCoverage93.cons _ _ compact93_node_0437
    (ChildrenCoverage93.cons _ _ compact93_node_0438
    (ChildrenCoverage93.cons _ _ compact93_node_0439
    (ChildrenCoverage93.cons _ _ compact93_node_0440
    (ChildrenCoverage93.cons _ _ compact93_node_0441
    (ChildrenCoverage93.cons _ _ compact93_node_0442
    (ChildrenCoverage93.cons _ _ compact93_node_0443
    (ChildrenCoverage93.cons _ _ compact93_node_0444
    (ChildrenCoverage93.cons _ _ compact93_node_0445
    (ChildrenCoverage93.cons _ _ compact93_node_0446
    (ChildrenCoverage93.cons _ _ compact93_node_0447
    (ChildrenCoverage93.cons _ _ compact93_node_0448
    (ChildrenCoverage93.cons _ _ compact93_node_0449
    (ChildrenCoverage93.cons _ _ compact93_node_0450
    (ChildrenCoverage93.cons _ _ compact93_node_0451
    (ChildrenCoverage93.cons _ _ compact93_node_0452
    (ChildrenCoverage93.cons _ _ compact93_node_0453
    (ChildrenCoverage93.cons _ _ compact93_node_0454
    (ChildrenCoverage93.cons _ _ compact93_node_0455
    (ChildrenCoverage93.cons _ _ compact93_node_0456
    (ChildrenCoverage93.cons _ _ compact93_node_0457
    (ChildrenCoverage93.cons _ _ compact93_node_0458
    (ChildrenCoverage93.cons _ _ compact93_node_0459
    (ChildrenCoverage93.cons _ _ compact93_node_0460
    (ChildrenCoverage93.cons _ _ compact93_node_0461
    (ChildrenCoverage93.cons _ _ compact93_node_0462
    (ChildrenCoverage93.cons _ _ compact93_node_0463
    (ChildrenCoverage93.cons _ _ compact93_node_0464
    (ChildrenCoverage93.cons _ _ compact93_node_0465
    (ChildrenCoverage93.cons _ _ compact93_node_0466
    (ChildrenCoverage93.cons _ _ compact93_node_0467
    (ChildrenCoverage93.cons _ _ compact93_node_0468
    (ChildrenCoverage93.cons _ _ compact93_node_0469
    (ChildrenCoverage93.cons _ _ compact93_node_0470
    (ChildrenCoverage93.cons _ _ compact93_node_0471
    (ChildrenCoverage93.cons _ _ compact93_node_0472
    ChildrenCoverage93.nil)))))))))))))))))))))))))))))))))))))))

theorem compact93_node_0474 : NodeCoverage93 [41] 41 52 :=
  demand_node_prune93 41 compact93_demands_41 compact93_demands_41_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0475 : NodeCoverage93 [40,40,13] 13 0 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0476 : NodeCoverage93 [40,40,10] 10 3 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0477 : NodeCoverage93 [40,40,9] 9 4 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0478 : NodeCoverage93 [40,40,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0479 : NodeCoverage93 [40,40,7] 7 6 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
