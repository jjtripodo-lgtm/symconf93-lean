module
public import Symconf93.CoverageShard93_040

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1490 : NodeCoverage93 [25,25,15] 15 28 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1491 : NodeCoverage93 [25,25,14] 14 29 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1492 : NodeCoverage93 [25,25,13] 13 30 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1493 : NodeCoverage93 [25,25,12] 12 31 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1494 : NodeCoverage93 [25,25,11] 11 32 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1495 : NodeCoverage93 [25,25,10] 10 33 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1496 : NodeCoverage93 [25,25,9] 9 34 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1497 : NodeCoverage93 [25,25,8] 8 35 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1498 : NodeCoverage93 [25,25,7] 7 36 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1499 : NodeCoverage93 [25,25,6] 6 37 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1500 : NodeCoverage93 [25,25,5] 5 38 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1501 : NodeCoverage93 [25,25,3] 3 40 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1502 : NodeCoverage93 [25,25] 25 43 :=
  node_fork93 (B := [25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1480
    (ChildrenCoverage93.cons _ _ compact93_node_1481
    (ChildrenCoverage93.cons _ _ compact93_node_1482
    (ChildrenCoverage93.cons _ _ compact93_node_1483
    (ChildrenCoverage93.cons _ _ compact93_node_1484
    (ChildrenCoverage93.cons _ _ compact93_node_1485
    (ChildrenCoverage93.cons _ _ compact93_node_1486
    (ChildrenCoverage93.cons _ _ compact93_node_1487
    (ChildrenCoverage93.cons _ _ compact93_node_1488
    (ChildrenCoverage93.cons _ _ compact93_node_1489
    (ChildrenCoverage93.cons _ _ compact93_node_1490
    (ChildrenCoverage93.cons _ _ compact93_node_1491
    (ChildrenCoverage93.cons _ _ compact93_node_1492
    (ChildrenCoverage93.cons _ _ compact93_node_1493
    (ChildrenCoverage93.cons _ _ compact93_node_1494
    (ChildrenCoverage93.cons _ _ compact93_node_1495
    (ChildrenCoverage93.cons _ _ compact93_node_1496
    (ChildrenCoverage93.cons _ _ compact93_node_1497
    (ChildrenCoverage93.cons _ _ compact93_node_1498
    (ChildrenCoverage93.cons _ _ compact93_node_1499
    (ChildrenCoverage93.cons _ _ compact93_node_1500
    (ChildrenCoverage93.cons _ _ compact93_node_1501
    ChildrenCoverage93.nil))))))))))))))))))))))

theorem compact93_node_1503 : NodeCoverage93 [25,24] 24 44 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1504 : NodeCoverage93 [25,23] 23 45 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1505 : NodeCoverage93 [25,22] 22 46 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1506 : NodeCoverage93 [25,21] 21 47 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1507 : NodeCoverage93 [25,20] 20 48 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1508 : NodeCoverage93 [25,19] 19 49 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1509 : NodeCoverage93 [25,18] 18 50 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1510 : NodeCoverage93 [25,17] 17 51 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1511 : NodeCoverage93 [25,16] 16 52 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1512 : NodeCoverage93 [25,15] 15 53 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1513 : NodeCoverage93 [25,14] 14 54 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1514 : NodeCoverage93 [25,13] 13 55 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1515 : NodeCoverage93 [25,12] 12 56 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1516 : NodeCoverage93 [25,11] 11 57 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1517 : NodeCoverage93 [25,10] 10 58 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1518 : NodeCoverage93 [25,9] 9 59 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1519 : NodeCoverage93 [25,8] 8 60 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1520 : NodeCoverage93 [25,7] 7 61 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1521 : NodeCoverage93 [25,6] 6 62 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1522 : NodeCoverage93 [25,5] 5 63 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1523 : NodeCoverage93 [25,3] 3 65 :=
  demand_node_prune93 25 compact93_demands_25 compact93_demands_25_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1524 : NodeCoverage93 [25] 25 68 :=
  node_fork93 (B := [25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1502
    (ChildrenCoverage93.cons _ _ compact93_node_1503
    (ChildrenCoverage93.cons _ _ compact93_node_1504
    (ChildrenCoverage93.cons _ _ compact93_node_1505
    (ChildrenCoverage93.cons _ _ compact93_node_1506
    (ChildrenCoverage93.cons _ _ compact93_node_1507
    (ChildrenCoverage93.cons _ _ compact93_node_1508
    (ChildrenCoverage93.cons _ _ compact93_node_1509
    (ChildrenCoverage93.cons _ _ compact93_node_1510
    (ChildrenCoverage93.cons _ _ compact93_node_1511
    (ChildrenCoverage93.cons _ _ compact93_node_1512
    (ChildrenCoverage93.cons _ _ compact93_node_1513
    (ChildrenCoverage93.cons _ _ compact93_node_1514
    (ChildrenCoverage93.cons _ _ compact93_node_1515
    (ChildrenCoverage93.cons _ _ compact93_node_1516
    (ChildrenCoverage93.cons _ _ compact93_node_1517
    (ChildrenCoverage93.cons _ _ compact93_node_1518
    (ChildrenCoverage93.cons _ _ compact93_node_1519
    (ChildrenCoverage93.cons _ _ compact93_node_1520
    (ChildrenCoverage93.cons _ _ compact93_node_1521
    (ChildrenCoverage93.cons _ _ compact93_node_1522
    (ChildrenCoverage93.cons _ _ compact93_node_1523
    ChildrenCoverage93.nil))))))))))))))))))))))

theorem compact93_node_1525 : NodeCoverage93 [24,24,24,21] 21 0 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1526 : NodeCoverage93 [24,24,24,18] 18 3 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1527 : NodeCoverage93 [24,24,24,17] 17 4 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1528 : NodeCoverage93 [24,24,24,16] 16 5 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1529 : NodeCoverage93 [24,24,24,15] 15 6 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1530 : NodeCoverage93 [24,24,24,14] 14 7 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1531 : NodeCoverage93 [24,24,24,13] 13 8 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1532 : NodeCoverage93 [24,24,24,12,9] 9 0 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1533 : NodeCoverage93 [24,24,24,12,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1534 : NodeCoverage93 [24,24,24,12,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1535 : NodeCoverage93 [24,24,24,12,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_1536 : NodeCoverage93 [24,24,24,12,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1535
    ChildrenCoverage93.nil)

theorem compact93_node_1537 : NodeCoverage93 [24,24,24,12,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1536
    ChildrenCoverage93.nil)

theorem compact93_node_1538 : NodeCoverage93 [24,24,24,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1532
    (ChildrenCoverage93.cons _ _ compact93_node_1533
    (ChildrenCoverage93.cons _ _ compact93_node_1534
    (ChildrenCoverage93.cons _ _ compact93_node_1537
    ChildrenCoverage93.nil))))

theorem compact93_node_1539 : NodeCoverage93 [24,24,24,11] 11 10 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1540 : NodeCoverage93 [24,24,24,10] 10 11 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1541 : NodeCoverage93 [24,24,24,9] 9 12 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1542 : NodeCoverage93 [24,24,24,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1543 : NodeCoverage93 [24,24,24,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1544 : NodeCoverage93 [24,24,24,6] 6 15 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1545 : NodeCoverage93 [24,24,24,5] 5 16 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
