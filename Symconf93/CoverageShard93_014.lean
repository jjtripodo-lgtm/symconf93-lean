module
public import Symconf93.CoverageShard93_013

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0764 : NodeCoverage93 [36,9,9,9,3] 3 27 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0765 : NodeCoverage93 [36,9,9,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0759
    (ChildrenCoverage93.cons _ _ compact93_node_0760
    (ChildrenCoverage93.cons _ _ compact93_node_0761
    (ChildrenCoverage93.cons _ _ compact93_node_0762
    (ChildrenCoverage93.cons _ _ compact93_node_0763
    (ChildrenCoverage93.cons _ _ compact93_node_0764
    ChildrenCoverage93.nil))))))

theorem compact93_node_0766 : NodeCoverage93 [36,9,9,8] 8 31 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0767 : NodeCoverage93 [36,9,9,7] 7 32 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0768 : NodeCoverage93 [36,9,9,6] 6 33 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0769 : NodeCoverage93 [36,9,9,5] 5 34 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0770 : NodeCoverage93 [36,9,9,3] 3 36 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0771 : NodeCoverage93 [36,9,9] 9 39 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0765
    (ChildrenCoverage93.cons _ _ compact93_node_0766
    (ChildrenCoverage93.cons _ _ compact93_node_0767
    (ChildrenCoverage93.cons _ _ compact93_node_0768
    (ChildrenCoverage93.cons _ _ compact93_node_0769
    (ChildrenCoverage93.cons _ _ compact93_node_0770
    ChildrenCoverage93.nil))))))

theorem compact93_node_0772 : NodeCoverage93 [36,9,8] 8 40 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0773 : NodeCoverage93 [36,9,7] 7 41 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0774 : NodeCoverage93 [36,9,6] 6 42 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0775 : NodeCoverage93 [36,9,5] 5 43 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0776 : NodeCoverage93 [36,9,3] 3 45 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0777 : NodeCoverage93 [36,9] 9 48 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0771
    (ChildrenCoverage93.cons _ _ compact93_node_0772
    (ChildrenCoverage93.cons _ _ compact93_node_0773
    (ChildrenCoverage93.cons _ _ compact93_node_0774
    (ChildrenCoverage93.cons _ _ compact93_node_0775
    (ChildrenCoverage93.cons _ _ compact93_node_0776
    ChildrenCoverage93.nil))))))

theorem compact93_node_0778 : NodeCoverage93 [36,8] 8 49 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0779 : NodeCoverage93 [36,7] 7 50 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0780 : NodeCoverage93 [36,6] 6 51 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0781 : NodeCoverage93 [36,5] 5 52 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0782 : NodeCoverage93 [36,3] 3 54 :=
  demand_node_prune93 36 compact93_demands_36 compact93_demands_36_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0783 : NodeCoverage93 [36] 36 57 :=
  node_fork93 (B := [36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0590
    (ChildrenCoverage93.cons _ _ compact93_node_0591
    (ChildrenCoverage93.cons _ _ compact93_node_0592
    (ChildrenCoverage93.cons _ _ compact93_node_0593
    (ChildrenCoverage93.cons _ _ compact93_node_0594
    (ChildrenCoverage93.cons _ _ compact93_node_0595
    (ChildrenCoverage93.cons _ _ compact93_node_0596
    (ChildrenCoverage93.cons _ _ compact93_node_0597
    (ChildrenCoverage93.cons _ _ compact93_node_0598
    (ChildrenCoverage93.cons _ _ compact93_node_0599
    (ChildrenCoverage93.cons _ _ compact93_node_0600
    (ChildrenCoverage93.cons _ _ compact93_node_0601
    (ChildrenCoverage93.cons _ _ compact93_node_0602
    (ChildrenCoverage93.cons _ _ compact93_node_0603
    (ChildrenCoverage93.cons _ _ compact93_node_0604
    (ChildrenCoverage93.cons _ _ compact93_node_0605
    (ChildrenCoverage93.cons _ _ compact93_node_0606
    (ChildrenCoverage93.cons _ _ compact93_node_0607
    (ChildrenCoverage93.cons _ _ compact93_node_0662
    (ChildrenCoverage93.cons _ _ compact93_node_0663
    (ChildrenCoverage93.cons _ _ compact93_node_0664
    (ChildrenCoverage93.cons _ _ compact93_node_0665
    (ChildrenCoverage93.cons _ _ compact93_node_0666
    (ChildrenCoverage93.cons _ _ compact93_node_0667
    (ChildrenCoverage93.cons _ _ compact93_node_0743
    (ChildrenCoverage93.cons _ _ compact93_node_0744
    (ChildrenCoverage93.cons _ _ compact93_node_0745
    (ChildrenCoverage93.cons _ _ compact93_node_0777
    (ChildrenCoverage93.cons _ _ compact93_node_0778
    (ChildrenCoverage93.cons _ _ compact93_node_0779
    (ChildrenCoverage93.cons _ _ compact93_node_0780
    (ChildrenCoverage93.cons _ _ compact93_node_0781
    (ChildrenCoverage93.cons _ _ compact93_node_0782
    ChildrenCoverage93.nil)))))))))))))))))))))))))))))))))

theorem compact93_node_0784 : NodeCoverage93 [35,35,23] 23 0 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0785 : NodeCoverage93 [35,35,20] 20 3 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0786 : NodeCoverage93 [35,35,19] 19 4 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0787 : NodeCoverage93 [35,35,18] 18 5 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0788 : NodeCoverage93 [35,35,17] 17 6 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0789 : NodeCoverage93 [35,35,16] 16 7 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0790 : NodeCoverage93 [35,35,15] 15 8 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0791 : NodeCoverage93 [35,35,14] 14 9 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0792 : NodeCoverage93 [35,35,13] 13 10 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0793 : NodeCoverage93 [35,35,12] 12 11 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0794 : NodeCoverage93 [35,35,11] 11 12 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0795 : NodeCoverage93 [35,35,10] 10 13 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0796 : NodeCoverage93 [35,35,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0797 : NodeCoverage93 [35,35,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0798 : NodeCoverage93 [35,35,7,7,6] 6 3 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0799 : NodeCoverage93 [35,35,7,7,5] 5 4 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0800 : NodeCoverage93 [35,35,7,7,3] 3 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0801 : NodeCoverage93 [35,35,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0798
    (ChildrenCoverage93.cons _ _ compact93_node_0799
    (ChildrenCoverage93.cons _ _ compact93_node_0800
    ChildrenCoverage93.nil)))

theorem compact93_node_0802 : NodeCoverage93 [35,35,7,6] 6 10 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0803 : NodeCoverage93 [35,35,7,5] 5 11 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0804 : NodeCoverage93 [35,35,7,3] 3 13 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0805 : NodeCoverage93 [35,35,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0801
    (ChildrenCoverage93.cons _ _ compact93_node_0802
    (ChildrenCoverage93.cons _ _ compact93_node_0803
    (ChildrenCoverage93.cons _ _ compact93_node_0804
    ChildrenCoverage93.nil))))

theorem compact93_node_0806 : NodeCoverage93 [35,35,6] 6 17 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0807 : NodeCoverage93 [35,35,5] 5 18 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0808 : NodeCoverage93 [35,35,3] 3 20 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0809 : NodeCoverage93 [35,35] 35 23 :=
  node_fork93 (B := [23,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0784
    (ChildrenCoverage93.cons _ _ compact93_node_0785
    (ChildrenCoverage93.cons _ _ compact93_node_0786
    (ChildrenCoverage93.cons _ _ compact93_node_0787
    (ChildrenCoverage93.cons _ _ compact93_node_0788
    (ChildrenCoverage93.cons _ _ compact93_node_0789
    (ChildrenCoverage93.cons _ _ compact93_node_0790
    (ChildrenCoverage93.cons _ _ compact93_node_0791
    (ChildrenCoverage93.cons _ _ compact93_node_0792
    (ChildrenCoverage93.cons _ _ compact93_node_0793
    (ChildrenCoverage93.cons _ _ compact93_node_0794
    (ChildrenCoverage93.cons _ _ compact93_node_0795
    (ChildrenCoverage93.cons _ _ compact93_node_0796
    (ChildrenCoverage93.cons _ _ compact93_node_0797
    (ChildrenCoverage93.cons _ _ compact93_node_0805
    (ChildrenCoverage93.cons _ _ compact93_node_0806
    (ChildrenCoverage93.cons _ _ compact93_node_0807
    (ChildrenCoverage93.cons _ _ compact93_node_0808
    ChildrenCoverage93.nil))))))))))))))))))

theorem compact93_node_0810 : NodeCoverage93 [35,34] 34 24 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0811 : NodeCoverage93 [35,33] 33 25 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0812 : NodeCoverage93 [35,32] 32 26 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0813 : NodeCoverage93 [35,31] 31 27 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0814 : NodeCoverage93 [35,30] 30 28 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0815 : NodeCoverage93 [35,29] 29 29 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0816 : NodeCoverage93 [35,28] 28 30 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0817 : NodeCoverage93 [35,27] 27 31 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0818 : NodeCoverage93 [35,26] 26 32 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0819 : NodeCoverage93 [35,25] 25 33 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0820 : NodeCoverage93 [35,24] 24 34 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0821 : NodeCoverage93 [35,23] 23 35 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0822 : NodeCoverage93 [35,22] 22 36 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0823 : NodeCoverage93 [35,21] 21 37 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0824 : NodeCoverage93 [35,20] 20 38 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0825 : NodeCoverage93 [35,19] 19 39 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0826 : NodeCoverage93 [35,18] 18 40 :=
  demand_node_prune93 35 compact93_demands_35 compact93_demands_35_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
