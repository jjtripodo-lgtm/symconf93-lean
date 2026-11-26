module
public import Symconf93.CoverageShard93_012

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0709 : NodeCoverage93 [36,12,12,5] 5 28 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0710 : NodeCoverage93 [36,12,12,3] 3 30 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0711 : NodeCoverage93 [36,12,12] 12 33 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0688
    (ChildrenCoverage93.cons _ _ compact93_node_0689
    (ChildrenCoverage93.cons _ _ compact93_node_0690
    (ChildrenCoverage93.cons _ _ compact93_node_0705
    (ChildrenCoverage93.cons _ _ compact93_node_0706
    (ChildrenCoverage93.cons _ _ compact93_node_0707
    (ChildrenCoverage93.cons _ _ compact93_node_0708
    (ChildrenCoverage93.cons _ _ compact93_node_0709
    (ChildrenCoverage93.cons _ _ compact93_node_0710
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0712 : NodeCoverage93 [36,12,11] 11 34 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0713 : NodeCoverage93 [36,12,10] 10 35 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0714 : NodeCoverage93 [36,12,9,9,9,9] 9 9 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0715 : NodeCoverage93 [36,12,9,9,9,8] 8 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0716 : NodeCoverage93 [36,12,9,9,9,7] 7 11 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0717 : NodeCoverage93 [36,12,9,9,9,6,6,6] 6 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0718 : NodeCoverage93 [36,12,9,9,9,6,6,3] 3 3 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0719 : NodeCoverage93 [36,12,9,9,9,6,6] 6 6 :=
  node_fork93 (B := [6,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0717
    (ChildrenCoverage93.cons _ _ compact93_node_0718
    ChildrenCoverage93.nil))

theorem compact93_node_0720 : NodeCoverage93 [36,12,9,9,9,6,5] 5 7 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0721 : NodeCoverage93 [36,12,9,9,9,6,3] 3 9 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0722 : NodeCoverage93 [36,12,9,9,9,6] 6 12 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0719
    (ChildrenCoverage93.cons _ _ compact93_node_0720
    (ChildrenCoverage93.cons _ _ compact93_node_0721
    ChildrenCoverage93.nil)))

theorem compact93_node_0723 : NodeCoverage93 [36,12,9,9,9,5] 5 13 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0724 : NodeCoverage93 [36,12,9,9,9,3] 3 15 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0725 : NodeCoverage93 [36,12,9,9,9] 9 18 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0714
    (ChildrenCoverage93.cons _ _ compact93_node_0715
    (ChildrenCoverage93.cons _ _ compact93_node_0716
    (ChildrenCoverage93.cons _ _ compact93_node_0722
    (ChildrenCoverage93.cons _ _ compact93_node_0723
    (ChildrenCoverage93.cons _ _ compact93_node_0724
    ChildrenCoverage93.nil))))))

theorem compact93_node_0726 : NodeCoverage93 [36,12,9,9,8] 8 19 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0727 : NodeCoverage93 [36,12,9,9,7] 7 20 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0728 : NodeCoverage93 [36,12,9,9,6] 6 21 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0729 : NodeCoverage93 [36,12,9,9,5] 5 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0730 : NodeCoverage93 [36,12,9,9,3] 3 24 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0731 : NodeCoverage93 [36,12,9,9] 9 27 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0725
    (ChildrenCoverage93.cons _ _ compact93_node_0726
    (ChildrenCoverage93.cons _ _ compact93_node_0727
    (ChildrenCoverage93.cons _ _ compact93_node_0728
    (ChildrenCoverage93.cons _ _ compact93_node_0729
    (ChildrenCoverage93.cons _ _ compact93_node_0730
    ChildrenCoverage93.nil))))))

theorem compact93_node_0732 : NodeCoverage93 [36,12,9,8] 8 28 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0733 : NodeCoverage93 [36,12,9,7] 7 29 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0734 : NodeCoverage93 [36,12,9,6] 6 30 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0735 : NodeCoverage93 [36,12,9,5] 5 31 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0736 : NodeCoverage93 [36,12,9,3] 3 33 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0737 : NodeCoverage93 [36,12,9] 9 36 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0731
    (ChildrenCoverage93.cons _ _ compact93_node_0732
    (ChildrenCoverage93.cons _ _ compact93_node_0733
    (ChildrenCoverage93.cons _ _ compact93_node_0734
    (ChildrenCoverage93.cons _ _ compact93_node_0735
    (ChildrenCoverage93.cons _ _ compact93_node_0736
    ChildrenCoverage93.nil))))))

theorem compact93_node_0738 : NodeCoverage93 [36,12,8] 8 37 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0739 : NodeCoverage93 [36,12,7] 7 38 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0740 : NodeCoverage93 [36,12,6] 6 39 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0741 : NodeCoverage93 [36,12,5] 5 40 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0742 : NodeCoverage93 [36,12,3] 3 42 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0743 : NodeCoverage93 [36,12] 12 45 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0711
    (ChildrenCoverage93.cons _ _ compact93_node_0712
    (ChildrenCoverage93.cons _ _ compact93_node_0713
    (ChildrenCoverage93.cons _ _ compact93_node_0737
    (ChildrenCoverage93.cons _ _ compact93_node_0738
    (ChildrenCoverage93.cons _ _ compact93_node_0739
    (ChildrenCoverage93.cons _ _ compact93_node_0740
    (ChildrenCoverage93.cons _ _ compact93_node_0741
    (ChildrenCoverage93.cons _ _ compact93_node_0742
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_0744 : NodeCoverage93 [36,11] 11 46 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0745 : NodeCoverage93 [36,10] 10 47 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0746 : NodeCoverage93 [36,9,9,9,9,9] 9 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0747 : NodeCoverage93 [36,9,9,9,9,8] 8 13 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0748 : NodeCoverage93 [36,9,9,9,9,7] 7 14 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0749 : NodeCoverage93 [36,9,9,9,9,6,6,6,3] 3 0 :=
  node_no_weak_demand93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0750 : NodeCoverage93 [36,9,9,9,9,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0749
    ChildrenCoverage93.nil)

theorem compact93_node_0751 : NodeCoverage93 [36,9,9,9,9,6,6,5] 5 4 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0752 : NodeCoverage93 [36,9,9,9,9,6,6,3] 3 6 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0753 : NodeCoverage93 [36,9,9,9,9,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0750
    (ChildrenCoverage93.cons _ _ compact93_node_0751
    (ChildrenCoverage93.cons _ _ compact93_node_0752
    ChildrenCoverage93.nil)))

theorem compact93_node_0754 : NodeCoverage93 [36,9,9,9,9,6,5] 5 10 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0755 : NodeCoverage93 [36,9,9,9,9,6,3] 3 12 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0756 : NodeCoverage93 [36,9,9,9,9,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0753
    (ChildrenCoverage93.cons _ _ compact93_node_0754
    (ChildrenCoverage93.cons _ _ compact93_node_0755
    ChildrenCoverage93.nil)))

theorem compact93_node_0757 : NodeCoverage93 [36,9,9,9,9,5] 5 16 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0758 : NodeCoverage93 [36,9,9,9,9,3] 3 18 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0759 : NodeCoverage93 [36,9,9,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0746
    (ChildrenCoverage93.cons _ _ compact93_node_0747
    (ChildrenCoverage93.cons _ _ compact93_node_0748
    (ChildrenCoverage93.cons _ _ compact93_node_0756
    (ChildrenCoverage93.cons _ _ compact93_node_0757
    (ChildrenCoverage93.cons _ _ compact93_node_0758
    ChildrenCoverage93.nil))))))

theorem compact93_node_0760 : NodeCoverage93 [36,9,9,9,8] 8 22 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0761 : NodeCoverage93 [36,9,9,9,7] 7 23 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0762 : NodeCoverage93 [36,9,9,9,6] 6 24 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0763 : NodeCoverage93 [36,9,9,9,5] 5 25 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
