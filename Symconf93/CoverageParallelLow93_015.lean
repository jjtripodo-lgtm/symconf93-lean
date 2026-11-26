module
public import Symconf93.CoverageParallelLow93_014

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2734 : NodeCoverage93 [16,15,15] 15 47 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2735 : NodeCoverage93 [16,15,14] 14 48 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2736 : NodeCoverage93 [16,15,13] 13 49 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2737 : NodeCoverage93 [16,15,12] 12 50 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2738 : NodeCoverage93 [16,15,11] 11 51 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2739 : NodeCoverage93 [16,15,10] 10 52 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2740 : NodeCoverage93 [16,15,9] 9 53 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2741 : NodeCoverage93 [16,15,8] 8 54 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2742 : NodeCoverage93 [16,15,7] 7 55 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2743 : NodeCoverage93 [16,15,6] 6 56 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2744 : NodeCoverage93 [16,15,5] 5 57 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2745 : NodeCoverage93 [16,15,3] 3 59 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2746 : NodeCoverage93 [16,15] 15 62 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2734
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2735
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2736
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2737
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2738
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2739
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2740
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2741
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2742
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2743
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2744
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2745
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2747 : NodeCoverage93 [16,14,14] 14 49 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2748 : NodeCoverage93 [16,14,13] 13 50 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2749 : NodeCoverage93 [16,14,12] 12 51 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2750 : NodeCoverage93 [16,14,11] 11 52 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2751 : NodeCoverage93 [16,14,10] 10 53 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2752 : NodeCoverage93 [16,14,9] 9 54 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2753 : NodeCoverage93 [16,14,8] 8 55 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2754 : NodeCoverage93 [16,14,7] 7 56 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2755 : NodeCoverage93 [16,14,6] 6 57 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2756 : NodeCoverage93 [16,14,5] 5 58 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2757 : NodeCoverage93 [16,14,3] 3 60 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2758 : NodeCoverage93 [16,14] 14 63 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2747
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2748
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2749
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2750
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2751
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2752
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2753
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2754
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2755
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2756
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2757
    ChildrenCoverage93.nil)))))))))))

theorem compact_parallel93_node_2759 : NodeCoverage93 [16,13,13] 13 51 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2760 : NodeCoverage93 [16,13,12] 12 52 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2761 : NodeCoverage93 [16,13,11] 11 53 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2762 : NodeCoverage93 [16,13,10] 10 54 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2763 : NodeCoverage93 [16,13,9] 9 55 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2764 : NodeCoverage93 [16,13,8] 8 56 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2765 : NodeCoverage93 [16,13,7] 7 57 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2766 : NodeCoverage93 [16,13,6] 6 58 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2767 : NodeCoverage93 [16,13,5] 5 59 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2768 : NodeCoverage93 [16,13,3] 3 61 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2769 : NodeCoverage93 [16,13] 13 64 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2759
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2760
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2761
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2762
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2763
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2764
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2765
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2766
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2767
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2768
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_2770 : NodeCoverage93 [16,12,12] 12 53 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2771 : NodeCoverage93 [16,12,11] 11 54 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2772 : NodeCoverage93 [16,12,10] 10 55 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2773 : NodeCoverage93 [16,12,9,9] 9 47 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2774 : NodeCoverage93 [16,12,9,8] 8 48 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2775 : NodeCoverage93 [16,12,9,7] 7 49 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2776 : NodeCoverage93 [16,12,9,6] 6 50 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2777 : NodeCoverage93 [16,12,9,5] 5 51 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2778 : NodeCoverage93 [16,12,9,3] 3 53 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2779 : NodeCoverage93 [16,12,9] 9 56 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2773
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2774
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2775
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2776
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2777
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2778
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2780 : NodeCoverage93 [16,12,8] 8 57 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2781 : NodeCoverage93 [16,12,7] 7 58 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2782 : NodeCoverage93 [16,12,6] 6 59 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2783 : NodeCoverage93 [16,12,5] 5 60 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2784 : NodeCoverage93 [16,12,3] 3 62 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2785 : NodeCoverage93 [16,12] 12 65 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2770
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2771
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2772
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2779
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2780
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2781
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2782
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2783
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2784
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_2786 : NodeCoverage93 [16,11,11] 11 55 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2787 : NodeCoverage93 [16,11,10] 10 56 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2788 : NodeCoverage93 [16,11,9] 9 57 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2789 : NodeCoverage93 [16,11,8] 8 58 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2790 : NodeCoverage93 [16,11,7] 7 59 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2791 : NodeCoverage93 [16,11,6] 6 60 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2792 : NodeCoverage93 [16,11,5] 5 61 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2793 : NodeCoverage93 [16,11,3] 3 63 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2794 : NodeCoverage93 [16,11] 11 66 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2786
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2787
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2788
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2789
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2790
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2791
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2792
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2793
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_2795 : NodeCoverage93 [16,10,10,10] 10 47 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2796 : NodeCoverage93 [16,10,10,9] 9 48 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2797 : NodeCoverage93 [16,10,10,8] 8 49 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2798 : NodeCoverage93 [16,10,10,7] 7 50 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2799 : NodeCoverage93 [16,10,10,6] 6 51 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2800 : NodeCoverage93 [16,10,10,5] 5 52 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2801 : NodeCoverage93 [16,10,10,3] 3 54 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2802 : NodeCoverage93 [16,10,10] 10 57 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2795
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2796
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2797
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2798
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2799
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2800
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2801
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2803 : NodeCoverage93 [16,10,9] 9 58 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2804 : NodeCoverage93 [16,10,8] 8 59 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2805 : NodeCoverage93 [16,10,7] 7 60 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2806 : NodeCoverage93 [16,10,6] 6 61 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2807 : NodeCoverage93 [16,10,5] 5 62 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2808 : NodeCoverage93 [16,10,3] 3 64 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
