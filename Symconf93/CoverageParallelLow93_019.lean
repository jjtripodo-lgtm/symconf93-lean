module
public import Symconf93.CoverageParallelLow93_018

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2917 : NodeCoverage93 [15,3] 3 75 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2918 : NodeCoverage93 [15] 15 78 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2906
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2907
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2908
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2909
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2910
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2911
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2912
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2913
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2914
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2915
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2916
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2917
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2919 : NodeCoverage93 [14,14,14,14,14,14,9] 9 0 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2920 : NodeCoverage93 [14,14,14,14,14,14,6] 6 3 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2921 : NodeCoverage93 [14,14,14,14,14,14,5] 5 4 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2922 : NodeCoverage93 [14,14,14,14,14,14,3] 3 6 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2923 : NodeCoverage93 [14,14,14,14,14,14] 14 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2919
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2920
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2921
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2922
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2924 : NodeCoverage93 [14,14,14,14,14,13] 13 10 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2925 : NodeCoverage93 [14,14,14,14,14,12] 12 11 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2926 : NodeCoverage93 [14,14,14,14,14,11] 11 12 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2927 : NodeCoverage93 [14,14,14,14,14,10] 10 13 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2928 : NodeCoverage93 [14,14,14,14,14,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2929 : NodeCoverage93 [14,14,14,14,14,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2930 : NodeCoverage93 [14,14,14,14,14,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2931 : NodeCoverage93 [14,14,14,14,14,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2932 : NodeCoverage93 [14,14,14,14,14,7,7,3] 3 6 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2933 : NodeCoverage93 [14,14,14,14,14,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2930
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2931
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2932
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2934 : NodeCoverage93 [14,14,14,14,14,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2935 : NodeCoverage93 [14,14,14,14,14,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2936 : NodeCoverage93 [14,14,14,14,14,7,3] 3 13 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2937 : NodeCoverage93 [14,14,14,14,14,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2933
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2934
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2935
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2936
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2938 : NodeCoverage93 [14,14,14,14,14,6] 6 17 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2939 : NodeCoverage93 [14,14,14,14,14,5] 5 18 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2940 : NodeCoverage93 [14,14,14,14,14,3] 3 20 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2941 : NodeCoverage93 [14,14,14,14,14] 14 23 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2923
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2924
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2925
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2926
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2927
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2928
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2929
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2937
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2938
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2939
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2940
    ChildrenCoverage93.nil)))))))))))

theorem compact_parallel93_node_2942 : NodeCoverage93 [14,14,14,14,13] 13 24 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2943 : NodeCoverage93 [14,14,14,14,12] 12 25 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2944 : NodeCoverage93 [14,14,14,14,11] 11 26 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2945 : NodeCoverage93 [14,14,14,14,10] 10 27 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2946 : NodeCoverage93 [14,14,14,14,9] 9 28 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2947 : NodeCoverage93 [14,14,14,14,8] 8 29 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2948 : NodeCoverage93 [14,14,14,14,7,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2949 : NodeCoverage93 [14,14,14,14,7,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2950 : NodeCoverage93 [14,14,14,14,7,7,7,7,3] 3 6 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2951 : NodeCoverage93 [14,14,14,14,7,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2948
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2949
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2950
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2952 : NodeCoverage93 [14,14,14,14,7,7,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2953 : NodeCoverage93 [14,14,14,14,7,7,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2954 : NodeCoverage93 [14,14,14,14,7,7,7,3] 3 13 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2955 : NodeCoverage93 [14,14,14,14,7,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2951
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2952
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2953
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2954
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2956 : NodeCoverage93 [14,14,14,14,7,7,6] 6 17 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2957 : NodeCoverage93 [14,14,14,14,7,7,5] 5 18 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2958 : NodeCoverage93 [14,14,14,14,7,7,3] 3 20 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2959 : NodeCoverage93 [14,14,14,14,7,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2955
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2956
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2957
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2958
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2960 : NodeCoverage93 [14,14,14,14,7,6] 6 24 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2961 : NodeCoverage93 [14,14,14,14,7,5] 5 25 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2962 : NodeCoverage93 [14,14,14,14,7,3] 3 27 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2963 : NodeCoverage93 [14,14,14,14,7] 7 30 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2959
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2960
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2961
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2962
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2964 : NodeCoverage93 [14,14,14,14,6] 6 31 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2965 : NodeCoverage93 [14,14,14,14,5] 5 32 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2966 : NodeCoverage93 [14,14,14,14,3] 3 34 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2967 : NodeCoverage93 [14,14,14,14] 14 37 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2941
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2942
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2943
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2944
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2945
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2946
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2947
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2963
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2964
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2965
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2966
    ChildrenCoverage93.nil)))))))))))

theorem compact_parallel93_node_2968 : NodeCoverage93 [14,14,14,13] 13 38 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2969 : NodeCoverage93 [14,14,14,12] 12 39 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2970 : NodeCoverage93 [14,14,14,11] 11 40 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2971 : NodeCoverage93 [14,14,14,10] 10 41 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2972 : NodeCoverage93 [14,14,14,9] 9 42 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2973 : NodeCoverage93 [14,14,14,8] 8 43 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2974 : NodeCoverage93 [14,14,14,7,7,7,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2975 : NodeCoverage93 [14,14,14,7,7,7,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2976 : NodeCoverage93 [14,14,14,7,7,7,7,7,7,3] 3 6 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2977 : NodeCoverage93 [14,14,14,7,7,7,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2974
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2975
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2976
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2978 : NodeCoverage93 [14,14,14,7,7,7,7,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2979 : NodeCoverage93 [14,14,14,7,7,7,7,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2980 : NodeCoverage93 [14,14,14,7,7,7,7,7,3] 3 13 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2981 : NodeCoverage93 [14,14,14,7,7,7,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2977
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2978
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2979
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2980
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2982 : NodeCoverage93 [14,14,14,7,7,7,7,6] 6 17 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2983 : NodeCoverage93 [14,14,14,7,7,7,7,5] 5 18 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2984 : NodeCoverage93 [14,14,14,7,7,7,7,3] 3 20 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2985 : NodeCoverage93 [14,14,14,7,7,7,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2981
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2982
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2983
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2984
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2986 : NodeCoverage93 [14,14,14,7,7,7,6] 6 24 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2987 : NodeCoverage93 [14,14,14,7,7,7,5] 5 25 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2988 : NodeCoverage93 [14,14,14,7,7,7,3] 3 27 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2989 : NodeCoverage93 [14,14,14,7,7,7] 7 30 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2985
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2986
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2987
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2988
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2990 : NodeCoverage93 [14,14,14,7,7,6] 6 31 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2991 : NodeCoverage93 [14,14,14,7,7,5] 5 32 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
