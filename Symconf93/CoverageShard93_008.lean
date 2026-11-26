module
public import Symconf93.CoverageShard93_007

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0480 : NodeCoverage93 [40,40,6] 6 7 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0481 : NodeCoverage93 [40,40,5] 5 8 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0482 : NodeCoverage93 [40,40,3] 3 10 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0483 : NodeCoverage93 [40,40] 40 13 :=
  node_fork93 (B := [13,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0475
    (ChildrenCoverage93.cons _ _ compact93_node_0476
    (ChildrenCoverage93.cons _ _ compact93_node_0477
    (ChildrenCoverage93.cons _ _ compact93_node_0478
    (ChildrenCoverage93.cons _ _ compact93_node_0479
    (ChildrenCoverage93.cons _ _ compact93_node_0480
    (ChildrenCoverage93.cons _ _ compact93_node_0481
    (ChildrenCoverage93.cons _ _ compact93_node_0482
    ChildrenCoverage93.nil))))))))

theorem compact93_node_0484 : NodeCoverage93 [40,39] 39 14 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0485 : NodeCoverage93 [40,38] 38 15 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0486 : NodeCoverage93 [40,37] 37 16 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0487 : NodeCoverage93 [40,36] 36 17 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0488 : NodeCoverage93 [40,35] 35 18 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0489 : NodeCoverage93 [40,34] 34 19 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0490 : NodeCoverage93 [40,33] 33 20 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0491 : NodeCoverage93 [40,32] 32 21 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0492 : NodeCoverage93 [40,31] 31 22 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0493 : NodeCoverage93 [40,30] 30 23 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0494 : NodeCoverage93 [40,29] 29 24 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0495 : NodeCoverage93 [40,28] 28 25 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0496 : NodeCoverage93 [40,27] 27 26 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0497 : NodeCoverage93 [40,26] 26 27 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0498 : NodeCoverage93 [40,25] 25 28 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0499 : NodeCoverage93 [40,24] 24 29 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0500 : NodeCoverage93 [40,23] 23 30 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0501 : NodeCoverage93 [40,22] 22 31 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0502 : NodeCoverage93 [40,21] 21 32 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0503 : NodeCoverage93 [40,20,20] 20 13 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0504 : NodeCoverage93 [40,20,19] 19 14 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0505 : NodeCoverage93 [40,20,18] 18 15 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0506 : NodeCoverage93 [40,20,17] 17 16 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0507 : NodeCoverage93 [40,20,16] 16 17 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0508 : NodeCoverage93 [40,20,15] 15 18 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0509 : NodeCoverage93 [40,20,14] 14 19 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0510 : NodeCoverage93 [40,20,13] 13 20 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0511 : NodeCoverage93 [40,20,12] 12 21 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0512 : NodeCoverage93 [40,20,11] 11 22 :=
  demand_node_prune93 40 compact93_demands_40 compact93_demands_40_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
