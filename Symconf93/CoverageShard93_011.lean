module
public import Symconf93.CoverageShard93_010

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0604 : NodeCoverage93 [36,22] 22 35 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0605 : NodeCoverage93 [36,21] 21 36 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0606 : NodeCoverage93 [36,20] 20 37 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0607 : NodeCoverage93 [36,19] 19 38 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0608 : NodeCoverage93 [36,18,18] 18 21 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0609 : NodeCoverage93 [36,18,17] 17 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0610 : NodeCoverage93 [36,18,16] 16 23 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0611 : NodeCoverage93 [36,18,15] 15 24 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0612 : NodeCoverage93 [36,18,14] 14 25 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0613 : NodeCoverage93 [36,18,13] 13 26 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0614 : NodeCoverage93 [36,18,12,12] 12 15 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0615 : NodeCoverage93 [36,18,12,11] 11 16 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0616 : NodeCoverage93 [36,18,12,10] 10 17 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0617 : NodeCoverage93 [36,18,12,9,9] 9 9 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0618 : NodeCoverage93 [36,18,12,9,8] 8 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0619 : NodeCoverage93 [36,18,12,9,7] 7 11 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0620 : NodeCoverage93 [36,18,12,9,6,6,6] 6 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0621 : NodeCoverage93 [36,18,12,9,6,6,3] 3 3 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0622 : NodeCoverage93 [36,18,12,9,6,6] 6 6 :=
  node_fork93 (B := [6,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0620
    (ChildrenCoverage93.cons _ _ compact93_node_0621
    ChildrenCoverage93.nil))

theorem compact93_node_0623 : NodeCoverage93 [36,18,12,9,6,5] 5 7 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0624 : NodeCoverage93 [36,18,12,9,6,3] 3 9 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0625 : NodeCoverage93 [36,18,12,9,6] 6 12 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0622
    (ChildrenCoverage93.cons _ _ compact93_node_0623
    (ChildrenCoverage93.cons _ _ compact93_node_0624
    ChildrenCoverage93.nil)))

theorem compact93_node_0626 : NodeCoverage93 [36,18,12,9,5] 5 13 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0627 : NodeCoverage93 [36,18,12,9,3] 3 15 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0628 : NodeCoverage93 [36,18,12,9] 9 18 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0617
    (ChildrenCoverage93.cons _ _ compact93_node_0618
    (ChildrenCoverage93.cons _ _ compact93_node_0619
    (ChildrenCoverage93.cons _ _ compact93_node_0625
    (ChildrenCoverage93.cons _ _ compact93_node_0626
    (ChildrenCoverage93.cons _ _ compact93_node_0627
    ChildrenCoverage93.nil))))))

theorem compact93_node_0629 : NodeCoverage93 [36,18,12,8] 8 19 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0630 : NodeCoverage93 [36,18,12,7] 7 20 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0631 : NodeCoverage93 [36,18,12,6] 6 21 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0632 : NodeCoverage93 [36,18,12,5] 5 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0633 : NodeCoverage93 [36,18,12,3] 3 24 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0634 : NodeCoverage93 [36,18,12] 12 27 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0614
    (ChildrenCoverage93.cons _ _ compact93_node_0615
    (ChildrenCoverage93.cons _ _ compact93_node_0616
    (ChildrenCoverage93.cons _ _ compact93_node_0628
    (ChildrenCoverage93.cons _ _ compact93_node_0629
    (ChildrenCoverage93.cons _ _ compact93_node_0630
    (ChildrenCoverage93.cons _ _ compact93_node_0631
    (ChildrenCoverage93.cons _ _ compact93_node_0632
    (ChildrenCoverage93.cons _ _ compact93_node_0633
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0635 : NodeCoverage93 [36,18,11] 11 28 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0636 : NodeCoverage93 [36,18,10] 10 29 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0637 : NodeCoverage93 [36,18,9,9,9,9,3] 3 0 :=
  node_no_weak_demand93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0638 : NodeCoverage93 [36,18,9,9,9,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0637
    ChildrenCoverage93.nil)

theorem compact93_node_0639 : NodeCoverage93 [36,18,9,9,9,8] 8 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0640 : NodeCoverage93 [36,18,9,9,9,7] 7 5 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0641 : NodeCoverage93 [36,18,9,9,9,6] 6 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0642 : NodeCoverage93 [36,18,9,9,9,5] 5 7 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0643 : NodeCoverage93 [36,18,9,9,9,3] 3 9 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0644 : NodeCoverage93 [36,18,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0638
    (ChildrenCoverage93.cons _ _ compact93_node_0639
    (ChildrenCoverage93.cons _ _ compact93_node_0640
    (ChildrenCoverage93.cons _ _ compact93_node_0641
    (ChildrenCoverage93.cons _ _ compact93_node_0642
    (ChildrenCoverage93.cons _ _ compact93_node_0643
    ChildrenCoverage93.nil))))))

theorem compact93_node_0645 : NodeCoverage93 [36,18,9,9,8] 8 13 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0646 : NodeCoverage93 [36,18,9,9,7] 7 14 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0647 : NodeCoverage93 [36,18,9,9,6] 6 15 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0648 : NodeCoverage93 [36,18,9,9,5] 5 16 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0649 : NodeCoverage93 [36,18,9,9,3] 3 18 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0650 : NodeCoverage93 [36,18,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0644
    (ChildrenCoverage93.cons _ _ compact93_node_0645
    (ChildrenCoverage93.cons _ _ compact93_node_0646
    (ChildrenCoverage93.cons _ _ compact93_node_0647
    (ChildrenCoverage93.cons _ _ compact93_node_0648
    (ChildrenCoverage93.cons _ _ compact93_node_0649
    ChildrenCoverage93.nil))))))

theorem compact93_node_0651 : NodeCoverage93 [36,18,9,8] 8 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0652 : NodeCoverage93 [36,18,9,7] 7 23 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0653 : NodeCoverage93 [36,18,9,6] 6 24 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0654 : NodeCoverage93 [36,18,9,5] 5 25 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
