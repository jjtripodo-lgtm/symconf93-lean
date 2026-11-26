module
public import Symconf93.CoverageShard93_011

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0655 : NodeCoverage93 [36,18,9,3] 3 27 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0656 : NodeCoverage93 [36,18,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0650
    (ChildrenCoverage93.cons _ _ compact93_node_0651
    (ChildrenCoverage93.cons _ _ compact93_node_0652
    (ChildrenCoverage93.cons _ _ compact93_node_0653
    (ChildrenCoverage93.cons _ _ compact93_node_0654
    (ChildrenCoverage93.cons _ _ compact93_node_0655
    ChildrenCoverage93.nil))))))

theorem compact93_node_0657 : NodeCoverage93 [36,18,8] 8 31 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0658 : NodeCoverage93 [36,18,7] 7 32 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0659 : NodeCoverage93 [36,18,6] 6 33 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0660 : NodeCoverage93 [36,18,5] 5 34 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0661 : NodeCoverage93 [36,18,3] 3 36 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0662 : NodeCoverage93 [36,18] 18 39 :=
  node_fork93 (B := [18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0608
    (ChildrenCoverage93.cons _ _ compact93_node_0609
    (ChildrenCoverage93.cons _ _ compact93_node_0610
    (ChildrenCoverage93.cons _ _ compact93_node_0611
    (ChildrenCoverage93.cons _ _ compact93_node_0612
    (ChildrenCoverage93.cons _ _ compact93_node_0613
    (ChildrenCoverage93.cons _ _ compact93_node_0634
    (ChildrenCoverage93.cons _ _ compact93_node_0635
    (ChildrenCoverage93.cons _ _ compact93_node_0636
    (ChildrenCoverage93.cons _ _ compact93_node_0656
    (ChildrenCoverage93.cons _ _ compact93_node_0657
    (ChildrenCoverage93.cons _ _ compact93_node_0658
    (ChildrenCoverage93.cons _ _ compact93_node_0659
    (ChildrenCoverage93.cons _ _ compact93_node_0660
    (ChildrenCoverage93.cons _ _ compact93_node_0661
    ChildrenCoverage93.nil)))))))))))))))

theorem compact93_node_0663 : NodeCoverage93 [36,17] 17 40 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0664 : NodeCoverage93 [36,16] 16 41 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0665 : NodeCoverage93 [36,15] 15 42 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0666 : NodeCoverage93 [36,14] 14 43 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0667 : NodeCoverage93 [36,13] 13 44 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0668 : NodeCoverage93 [36,12,12,12,12,9] 9 0 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0669 : NodeCoverage93 [36,12,12,12,12,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0670 : NodeCoverage93 [36,12,12,12,12,5] 5 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0671 : NodeCoverage93 [36,12,12,12,12,3] 3 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0672 : NodeCoverage93 [36,12,12,12,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0668
    (ChildrenCoverage93.cons _ _ compact93_node_0669
    (ChildrenCoverage93.cons _ _ compact93_node_0670
    (ChildrenCoverage93.cons _ _ compact93_node_0671
    ChildrenCoverage93.nil))))

theorem compact93_node_0673 : NodeCoverage93 [36,12,12,12,11] 11 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0674 : NodeCoverage93 [36,12,12,12,10] 10 11 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0675 : NodeCoverage93 [36,12,12,12,9] 9 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0676 : NodeCoverage93 [36,12,12,12,8] 8 13 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0677 : NodeCoverage93 [36,12,12,12,7] 7 14 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0678 : NodeCoverage93 [36,12,12,12,6,6,6,3] 3 0 :=
  node_no_weak_demand93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0679 : NodeCoverage93 [36,12,12,12,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0678
    ChildrenCoverage93.nil)

theorem compact93_node_0680 : NodeCoverage93 [36,12,12,12,6,6,5] 5 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0681 : NodeCoverage93 [36,12,12,12,6,6,3] 3 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0682 : NodeCoverage93 [36,12,12,12,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0679
    (ChildrenCoverage93.cons _ _ compact93_node_0680
    (ChildrenCoverage93.cons _ _ compact93_node_0681
    ChildrenCoverage93.nil)))

theorem compact93_node_0683 : NodeCoverage93 [36,12,12,12,6,5] 5 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0684 : NodeCoverage93 [36,12,12,12,6,3] 3 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0685 : NodeCoverage93 [36,12,12,12,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0682
    (ChildrenCoverage93.cons _ _ compact93_node_0683
    (ChildrenCoverage93.cons _ _ compact93_node_0684
    ChildrenCoverage93.nil)))

theorem compact93_node_0686 : NodeCoverage93 [36,12,12,12,5] 5 16 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0687 : NodeCoverage93 [36,12,12,12,3] 3 18 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0688 : NodeCoverage93 [36,12,12,12] 12 21 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0672
    (ChildrenCoverage93.cons _ _ compact93_node_0673
    (ChildrenCoverage93.cons _ _ compact93_node_0674
    (ChildrenCoverage93.cons _ _ compact93_node_0675
    (ChildrenCoverage93.cons _ _ compact93_node_0676
    (ChildrenCoverage93.cons _ _ compact93_node_0677
    (ChildrenCoverage93.cons _ _ compact93_node_0685
    (ChildrenCoverage93.cons _ _ compact93_node_0686
    (ChildrenCoverage93.cons _ _ compact93_node_0687
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0689 : NodeCoverage93 [36,12,12,11] 11 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0690 : NodeCoverage93 [36,12,12,10] 10 23 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0691 : NodeCoverage93 [36,12,12,9,9,9,6] 6 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0692 : NodeCoverage93 [36,12,12,9,9,9,3] 3 3 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0693 : NodeCoverage93 [36,12,12,9,9,9] 9 6 :=
  node_fork93 (B := [6,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0691
    (ChildrenCoverage93.cons _ _ compact93_node_0692
    ChildrenCoverage93.nil))

theorem compact93_node_0694 : NodeCoverage93 [36,12,12,9,9,8] 8 7 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0695 : NodeCoverage93 [36,12,12,9,9,7] 7 8 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0696 : NodeCoverage93 [36,12,12,9,9,6] 6 9 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0697 : NodeCoverage93 [36,12,12,9,9,5] 5 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0698 : NodeCoverage93 [36,12,12,9,9,3] 3 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0699 : NodeCoverage93 [36,12,12,9,9] 9 15 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0693
    (ChildrenCoverage93.cons _ _ compact93_node_0694
    (ChildrenCoverage93.cons _ _ compact93_node_0695
    (ChildrenCoverage93.cons _ _ compact93_node_0696
    (ChildrenCoverage93.cons _ _ compact93_node_0697
    (ChildrenCoverage93.cons _ _ compact93_node_0698
    ChildrenCoverage93.nil))))))

theorem compact93_node_0700 : NodeCoverage93 [36,12,12,9,8] 8 16 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0701 : NodeCoverage93 [36,12,12,9,7] 7 17 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0702 : NodeCoverage93 [36,12,12,9,6] 6 18 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0703 : NodeCoverage93 [36,12,12,9,5] 5 19 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0704 : NodeCoverage93 [36,12,12,9,3] 3 21 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0705 : NodeCoverage93 [36,12,12,9] 9 24 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0699
    (ChildrenCoverage93.cons _ _ compact93_node_0700
    (ChildrenCoverage93.cons _ _ compact93_node_0701
    (ChildrenCoverage93.cons _ _ compact93_node_0702
    (ChildrenCoverage93.cons _ _ compact93_node_0703
    (ChildrenCoverage93.cons _ _ compact93_node_0704
    ChildrenCoverage93.nil))))))

theorem compact93_node_0706 : NodeCoverage93 [36,12,12,8] 8 25 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0707 : NodeCoverage93 [36,12,12,7] 7 26 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0708 : NodeCoverage93 [36,12,12,6] 6 27 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
