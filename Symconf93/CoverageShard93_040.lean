module
public import Symconf93.CoverageShard93_039

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1427 : NodeCoverage93 [27,9,9,9,9,9,9,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1426
    ChildrenCoverage93.nil)

theorem compact93_node_1428 : NodeCoverage93 [27,9,9,9,9,9,9,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1427
    ChildrenCoverage93.nil)

theorem compact93_node_1429 : NodeCoverage93 [27,9,9,9,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1420
    (ChildrenCoverage93.cons _ _ compact93_node_1421
    (ChildrenCoverage93.cons _ _ compact93_node_1422
    (ChildrenCoverage93.cons _ _ compact93_node_1423
    (ChildrenCoverage93.cons _ _ compact93_node_1424
    (ChildrenCoverage93.cons _ _ compact93_node_1428
    ChildrenCoverage93.nil))))))

theorem compact93_node_1430 : NodeCoverage93 [27,9,9,9,9,9,8] 8 13 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1431 : NodeCoverage93 [27,9,9,9,9,9,7] 7 14 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1432 : NodeCoverage93 [27,9,9,9,9,9,6] 6 15 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1433 : NodeCoverage93 [27,9,9,9,9,9,5] 5 16 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1434 : NodeCoverage93 [27,9,9,9,9,9,3] 3 18 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1435 : NodeCoverage93 [27,9,9,9,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1429
    (ChildrenCoverage93.cons _ _ compact93_node_1430
    (ChildrenCoverage93.cons _ _ compact93_node_1431
    (ChildrenCoverage93.cons _ _ compact93_node_1432
    (ChildrenCoverage93.cons _ _ compact93_node_1433
    (ChildrenCoverage93.cons _ _ compact93_node_1434
    ChildrenCoverage93.nil))))))

theorem compact93_node_1436 : NodeCoverage93 [27,9,9,9,9,8] 8 22 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1437 : NodeCoverage93 [27,9,9,9,9,7] 7 23 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1438 : NodeCoverage93 [27,9,9,9,9,6] 6 24 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1439 : NodeCoverage93 [27,9,9,9,9,5] 5 25 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1440 : NodeCoverage93 [27,9,9,9,9,3] 3 27 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1441 : NodeCoverage93 [27,9,9,9,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1435
    (ChildrenCoverage93.cons _ _ compact93_node_1436
    (ChildrenCoverage93.cons _ _ compact93_node_1437
    (ChildrenCoverage93.cons _ _ compact93_node_1438
    (ChildrenCoverage93.cons _ _ compact93_node_1439
    (ChildrenCoverage93.cons _ _ compact93_node_1440
    ChildrenCoverage93.nil))))))

theorem compact93_node_1442 : NodeCoverage93 [27,9,9,9,8] 8 31 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1443 : NodeCoverage93 [27,9,9,9,7] 7 32 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1444 : NodeCoverage93 [27,9,9,9,6] 6 33 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1445 : NodeCoverage93 [27,9,9,9,5] 5 34 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1446 : NodeCoverage93 [27,9,9,9,3] 3 36 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1447 : NodeCoverage93 [27,9,9,9] 9 39 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1441
    (ChildrenCoverage93.cons _ _ compact93_node_1442
    (ChildrenCoverage93.cons _ _ compact93_node_1443
    (ChildrenCoverage93.cons _ _ compact93_node_1444
    (ChildrenCoverage93.cons _ _ compact93_node_1445
    (ChildrenCoverage93.cons _ _ compact93_node_1446
    ChildrenCoverage93.nil))))))

theorem compact93_node_1448 : NodeCoverage93 [27,9,9,8] 8 40 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1449 : NodeCoverage93 [27,9,9,7] 7 41 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1450 : NodeCoverage93 [27,9,9,6] 6 42 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1451 : NodeCoverage93 [27,9,9,5] 5 43 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1452 : NodeCoverage93 [27,9,9,3] 3 45 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1453 : NodeCoverage93 [27,9,9] 9 48 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1447
    (ChildrenCoverage93.cons _ _ compact93_node_1448
    (ChildrenCoverage93.cons _ _ compact93_node_1449
    (ChildrenCoverage93.cons _ _ compact93_node_1450
    (ChildrenCoverage93.cons _ _ compact93_node_1451
    (ChildrenCoverage93.cons _ _ compact93_node_1452
    ChildrenCoverage93.nil))))))

theorem compact93_node_1454 : NodeCoverage93 [27,9,8] 8 49 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1455 : NodeCoverage93 [27,9,7] 7 50 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1456 : NodeCoverage93 [27,9,6] 6 51 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1457 : NodeCoverage93 [27,9,5] 5 52 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1458 : NodeCoverage93 [27,9,3] 3 54 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1459 : NodeCoverage93 [27,9] 9 57 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1453
    (ChildrenCoverage93.cons _ _ compact93_node_1454
    (ChildrenCoverage93.cons _ _ compact93_node_1455
    (ChildrenCoverage93.cons _ _ compact93_node_1456
    (ChildrenCoverage93.cons _ _ compact93_node_1457
    (ChildrenCoverage93.cons _ _ compact93_node_1458
    ChildrenCoverage93.nil))))))

theorem compact93_node_1460 : NodeCoverage93 [27,8] 8 58 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1461 : NodeCoverage93 [27,7] 7 59 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1462 : NodeCoverage93 [27,6] 6 60 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1463 : NodeCoverage93 [27,5] 5 61 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1464 : NodeCoverage93 [27,3] 3 63 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1465 : NodeCoverage93 [27] 27 66 :=
  node_fork93 (B := [27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1377
    (ChildrenCoverage93.cons _ _ compact93_node_1378
    (ChildrenCoverage93.cons _ _ compact93_node_1379
    (ChildrenCoverage93.cons _ _ compact93_node_1380
    (ChildrenCoverage93.cons _ _ compact93_node_1381
    (ChildrenCoverage93.cons _ _ compact93_node_1382
    (ChildrenCoverage93.cons _ _ compact93_node_1383
    (ChildrenCoverage93.cons _ _ compact93_node_1384
    (ChildrenCoverage93.cons _ _ compact93_node_1385
    (ChildrenCoverage93.cons _ _ compact93_node_1386
    (ChildrenCoverage93.cons _ _ compact93_node_1387
    (ChildrenCoverage93.cons _ _ compact93_node_1388
    (ChildrenCoverage93.cons _ _ compact93_node_1389
    (ChildrenCoverage93.cons _ _ compact93_node_1390
    (ChildrenCoverage93.cons _ _ compact93_node_1391
    (ChildrenCoverage93.cons _ _ compact93_node_1401
    (ChildrenCoverage93.cons _ _ compact93_node_1410
    (ChildrenCoverage93.cons _ _ compact93_node_1418
    (ChildrenCoverage93.cons _ _ compact93_node_1459
    (ChildrenCoverage93.cons _ _ compact93_node_1460
    (ChildrenCoverage93.cons _ _ compact93_node_1461
    (ChildrenCoverage93.cons _ _ compact93_node_1462
    (ChildrenCoverage93.cons _ _ compact93_node_1463
    (ChildrenCoverage93.cons _ _ compact93_node_1464
    ChildrenCoverage93.nil))))))))))))))))))))))))

theorem compact93_node_1466 : NodeCoverage93 [26] 26 67 :=
  demand_node_prune93 26 compact93_demands_26 compact93_demands_26_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1467 : NodeCoverage93 [25,25,25,18] 18 0 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1468 : NodeCoverage93 [25,25,25,15] 15 3 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1469 : NodeCoverage93 [25,25,25,14] 14 4 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1470 : NodeCoverage93 [25,25,25,13] 13 5 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1471 : NodeCoverage93 [25,25,25,12] 12 6 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1472 : NodeCoverage93 [25,25,25,11] 11 7 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1473 : NodeCoverage93 [25,25,25,10] 10 8 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1474 : NodeCoverage93 [25,25,25,9] 9 9 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1475 : NodeCoverage93 [25,25,25,8] 8 10 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1476 : NodeCoverage93 [25,25,25,7] 7 11 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1477 : NodeCoverage93 [25,25,25,6] 6 12 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1478 : NodeCoverage93 [25,25,25,5] 5 13 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1479 : NodeCoverage93 [25,25,25,3] 3 15 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1480 : NodeCoverage93 [25,25,25] 25 18 :=
  node_fork93 (B := [18,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1467
    (ChildrenCoverage93.cons _ _ compact93_node_1468
    (ChildrenCoverage93.cons _ _ compact93_node_1469
    (ChildrenCoverage93.cons _ _ compact93_node_1470
    (ChildrenCoverage93.cons _ _ compact93_node_1471
    (ChildrenCoverage93.cons _ _ compact93_node_1472
    (ChildrenCoverage93.cons _ _ compact93_node_1473
    (ChildrenCoverage93.cons _ _ compact93_node_1474
    (ChildrenCoverage93.cons _ _ compact93_node_1475
    (ChildrenCoverage93.cons _ _ compact93_node_1476
    (ChildrenCoverage93.cons _ _ compact93_node_1477
    (ChildrenCoverage93.cons _ _ compact93_node_1478
    (ChildrenCoverage93.cons _ _ compact93_node_1479
    ChildrenCoverage93.nil)))))))))))))

theorem compact93_node_1481 : NodeCoverage93 [25,25,24] 24 19 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1482 : NodeCoverage93 [25,25,23] 23 20 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1483 : NodeCoverage93 [25,25,22] 22 21 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1484 : NodeCoverage93 [25,25,21] 21 22 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1485 : NodeCoverage93 [25,25,20] 20 23 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1486 : NodeCoverage93 [25,25,19] 19 24 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1487 : NodeCoverage93 [25,25,18] 18 25 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1488 : NodeCoverage93 [25,25,17] 17 26 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1489 : NodeCoverage93 [25,25,16] 16 27 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
