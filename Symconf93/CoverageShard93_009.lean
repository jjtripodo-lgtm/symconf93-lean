module
public import Symconf93.CoverageShard93_008

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0513 : NodeCoverage93 [40,20,10] 10 23 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0514 : NodeCoverage93 [40,20,9] 9 24 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0515 : NodeCoverage93 [40,20,8] 8 25 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0516 : NodeCoverage93 [40,20,7] 7 26 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0517 : NodeCoverage93 [40,20,6] 6 27 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0518 : NodeCoverage93 [40,20,5] 5 28 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0519 : NodeCoverage93 [40,20,3] 3 30 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0520 : NodeCoverage93 [40,20] 20 33 :=
  node_fork93 (B := [20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0503
    (ChildrenCoverage93.cons _ _ compact93_node_0504
    (ChildrenCoverage93.cons _ _ compact93_node_0505
    (ChildrenCoverage93.cons _ _ compact93_node_0506
    (ChildrenCoverage93.cons _ _ compact93_node_0507
    (ChildrenCoverage93.cons _ _ compact93_node_0508
    (ChildrenCoverage93.cons _ _ compact93_node_0509
    (ChildrenCoverage93.cons _ _ compact93_node_0510
    (ChildrenCoverage93.cons _ _ compact93_node_0511
    (ChildrenCoverage93.cons _ _ compact93_node_0512
    (ChildrenCoverage93.cons _ _ compact93_node_0513
    (ChildrenCoverage93.cons _ _ compact93_node_0514
    (ChildrenCoverage93.cons _ _ compact93_node_0515
    (ChildrenCoverage93.cons _ _ compact93_node_0516
    (ChildrenCoverage93.cons _ _ compact93_node_0517
    (ChildrenCoverage93.cons _ _ compact93_node_0518
    (ChildrenCoverage93.cons _ _ compact93_node_0519
    ChildrenCoverage93.nil)))))))))))))))))

theorem compact93_node_0521 : NodeCoverage93 [40,19] 19 34 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0522 : NodeCoverage93 [40,18] 18 35 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0523 : NodeCoverage93 [40,17] 17 36 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0524 : NodeCoverage93 [40,16] 16 37 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0525 : NodeCoverage93 [40,15] 15 38 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0526 : NodeCoverage93 [40,14] 14 39 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0527 : NodeCoverage93 [40,13] 13 40 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0528 : NodeCoverage93 [40,12] 12 41 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0529 : NodeCoverage93 [40,11] 11 42 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0530 : NodeCoverage93 [40,10,10,10,10] 10 13 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0531 : NodeCoverage93 [40,10,10,10,9] 9 14 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0532 : NodeCoverage93 [40,10,10,10,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0533 : NodeCoverage93 [40,10,10,10,7] 7 16 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0534 : NodeCoverage93 [40,10,10,10,6] 6 17 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0535 : NodeCoverage93 [40,10,10,10,5] 5 18 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0536 : NodeCoverage93 [40,10,10,10,3] 3 20 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0537 : NodeCoverage93 [40,10,10,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0530
    (ChildrenCoverage93.cons _ _ compact93_node_0531
    (ChildrenCoverage93.cons _ _ compact93_node_0532
    (ChildrenCoverage93.cons _ _ compact93_node_0533
    (ChildrenCoverage93.cons _ _ compact93_node_0534
    (ChildrenCoverage93.cons _ _ compact93_node_0535
    (ChildrenCoverage93.cons _ _ compact93_node_0536
    ChildrenCoverage93.nil)))))))

theorem compact93_node_0538 : NodeCoverage93 [40,10,10,9] 9 24 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0539 : NodeCoverage93 [40,10,10,8] 8 25 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0540 : NodeCoverage93 [40,10,10,7] 7 26 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0541 : NodeCoverage93 [40,10,10,6] 6 27 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0542 : NodeCoverage93 [40,10,10,5] 5 28 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0543 : NodeCoverage93 [40,10,10,3] 3 30 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0544 : NodeCoverage93 [40,10,10] 10 33 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0537
    (ChildrenCoverage93.cons _ _ compact93_node_0538
    (ChildrenCoverage93.cons _ _ compact93_node_0539
    (ChildrenCoverage93.cons _ _ compact93_node_0540
    (ChildrenCoverage93.cons _ _ compact93_node_0541
    (ChildrenCoverage93.cons _ _ compact93_node_0542
    (ChildrenCoverage93.cons _ _ compact93_node_0543
    ChildrenCoverage93.nil)))))))

theorem compact93_node_0545 : NodeCoverage93 [40,10,9] 9 34 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0546 : NodeCoverage93 [40,10,8] 8 35 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0547 : NodeCoverage93 [40,10,7] 7 36 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0548 : NodeCoverage93 [40,10,6] 6 37 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0549 : NodeCoverage93 [40,10,5] 5 38 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
