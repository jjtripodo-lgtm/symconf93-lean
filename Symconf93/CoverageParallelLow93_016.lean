module
public import Symconf93.CoverageParallelLow93_015

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2809 : NodeCoverage93 [16,10] 10 67 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2802
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2803
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2804
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2805
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2806
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2807
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2808
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2810 : NodeCoverage93 [16,9,9,9] 9 50 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2811 : NodeCoverage93 [16,9,9,8] 8 51 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2812 : NodeCoverage93 [16,9,9,7] 7 52 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2813 : NodeCoverage93 [16,9,9,6] 6 53 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2814 : NodeCoverage93 [16,9,9,5] 5 54 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2815 : NodeCoverage93 [16,9,9,3] 3 56 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2816 : NodeCoverage93 [16,9,9] 9 59 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2810
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2811
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2812
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2813
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2814
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2815
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2817 : NodeCoverage93 [16,9,8] 8 60 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2818 : NodeCoverage93 [16,9,7] 7 61 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2819 : NodeCoverage93 [16,9,6] 6 62 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2820 : NodeCoverage93 [16,9,5] 5 63 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2821 : NodeCoverage93 [16,9,3] 3 65 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2822 : NodeCoverage93 [16,9] 9 68 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2816
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2817
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2818
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2819
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2820
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2821
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2823 : NodeCoverage93 [16,8] 8 69 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2824 : NodeCoverage93 [16,7] 7 70 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2825 : NodeCoverage93 [16,6] 6 71 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2826 : NodeCoverage93 [16,5] 5 72 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2827 : NodeCoverage93 [16,3] 3 74 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2828 : NodeCoverage93 [16] 16 77 :=
  node_fork93 (B := [16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2733
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2746
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2758
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2769
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2785
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2794
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2809
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2822
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2823
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2824
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2825
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2826
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2827
    ChildrenCoverage93.nil)))))))))))))

theorem compact_parallel93_node_2829 : NodeCoverage93 [15,15,15,15,15,15,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_2830 : NodeCoverage93 [15,15,15,15,15,15] 15 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2829
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2831 : NodeCoverage93 [15,15,15,15,15,14] 14 4 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2832 : NodeCoverage93 [15,15,15,15,15,13] 13 5 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2833 : NodeCoverage93 [15,15,15,15,15,12] 12 6 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2834 : NodeCoverage93 [15,15,15,15,15,11] 11 7 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2835 : NodeCoverage93 [15,15,15,15,15,10] 10 8 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2836 : NodeCoverage93 [15,15,15,15,15,9] 9 9 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2837 : NodeCoverage93 [15,15,15,15,15,8] 8 10 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2838 : NodeCoverage93 [15,15,15,15,15,7] 7 11 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2839 : NodeCoverage93 [15,15,15,15,15,6] 6 12 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2840 : NodeCoverage93 [15,15,15,15,15,5,5,5,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_2841 : NodeCoverage93 [15,15,15,15,15,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2840
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2842 : NodeCoverage93 [15,15,15,15,15,5,5,3] 3 5 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2843 : NodeCoverage93 [15,15,15,15,15,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2841
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2842
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2844 : NodeCoverage93 [15,15,15,15,15,5,3] 3 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2845 : NodeCoverage93 [15,15,15,15,15,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2843
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2844
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2846 : NodeCoverage93 [15,15,15,15,15,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_2847 : NodeCoverage93 [15,15,15,15,15,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2846
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2848 : NodeCoverage93 [15,15,15,15,15,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2847
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2849 : NodeCoverage93 [15,15,15,15,15,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2848
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2850 : NodeCoverage93 [15,15,15,15,15,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2849
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2851 : NodeCoverage93 [15,15,15,15,15,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2850
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2852 : NodeCoverage93 [15,15,15,15,15] 15 18 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2830
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2831
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2832
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2833
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2834
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2835
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2836
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2837
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2838
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2839
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2845
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2851
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2853 : NodeCoverage93 [15,15,15,15,14] 14 19 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2854 : NodeCoverage93 [15,15,15,15,13] 13 20 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2855 : NodeCoverage93 [15,15,15,15,12] 12 21 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2856 : NodeCoverage93 [15,15,15,15,11] 11 22 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2857 : NodeCoverage93 [15,15,15,15,10] 10 23 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2858 : NodeCoverage93 [15,15,15,15,9] 9 24 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2859 : NodeCoverage93 [15,15,15,15,8] 8 25 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2860 : NodeCoverage93 [15,15,15,15,7] 7 26 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2861 : NodeCoverage93 [15,15,15,15,6] 6 27 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2862 : NodeCoverage93 [15,15,15,15,5,5,5,5,5,5,3] 3 0 :=
  node_no_weak_demand93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2863 : NodeCoverage93 [15,15,15,15,5,5,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2862
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2864 : NodeCoverage93 [15,15,15,15,5,5,5,5,5,3] 3 5 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact_parallel93_node_2865 : NodeCoverage93 [15,15,15,15,5,5,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2863
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2864
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2866 : NodeCoverage93 [15,15,15,15,5,5,5,5,3,3,3] 3 4 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact_parallel93_node_2867 : NodeCoverage93 [15,15,15,15,5,5,5,5,3,3] 3 7 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2866
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2868 : NodeCoverage93 [15,15,15,15,5,5,5,5,3] 3 10 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2867
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2869 : NodeCoverage93 [15,15,15,15,5,5,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2865
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2868
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2870 : NodeCoverage93 [15,15,15,15,5,5,5,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2871 : NodeCoverage93 [15,15,15,15,5,5,5,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2870
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2872 : NodeCoverage93 [15,15,15,15,5,5,5,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2871
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2873 : NodeCoverage93 [15,15,15,15,5,5,5,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2872
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2874 : NodeCoverage93 [15,15,15,15,5,5,5,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2873
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2875 : NodeCoverage93 [15,15,15,15,5,5,5,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2874
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2876 : NodeCoverage93 [15,15,15,15,5,5,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2869
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2875
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2877 : NodeCoverage93 [15,15,15,15,5,5,3] 3 20 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2878 : NodeCoverage93 [15,15,15,15,5,5] 5 23 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2876
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2877
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2879 : NodeCoverage93 [15,15,15,15,5,3] 3 25 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2880 : NodeCoverage93 [15,15,15,15,5] 5 28 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2878
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2879
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2881 : NodeCoverage93 [15,15,15,15,3] 3 30 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2882 : NodeCoverage93 [15,15,15,15] 15 33 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2852
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2853
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2854
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2855
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2856
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2857
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2858
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2859
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2860
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2861
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2880
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2881
    ChildrenCoverage93.nil))))))))))))

end Symconf93
