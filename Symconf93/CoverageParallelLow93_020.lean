module
public import Symconf93.CoverageParallelLow93_019

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2992 : NodeCoverage93 [14,14,14,7,7,3] 3 34 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2993 : NodeCoverage93 [14,14,14,7,7] 7 37 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2989
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2990
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2991
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2992
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2994 : NodeCoverage93 [14,14,14,7,6] 6 38 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2995 : NodeCoverage93 [14,14,14,7,5] 5 39 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2996 : NodeCoverage93 [14,14,14,7,3] 3 41 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2997 : NodeCoverage93 [14,14,14,7] 7 44 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2993
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2994
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2995
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2996
    ChildrenCoverage93.nil))))

theorem compact_parallel93_node_2998 : NodeCoverage93 [14,14,14,6] 6 45 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2999 : NodeCoverage93 [14,14,14,5] 5 46 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3000 : NodeCoverage93 [14,14,14,3] 3 48 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3001 : NodeCoverage93 [14,14,14] 14 51 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2967
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2968
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2969
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2970
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2971
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2972
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2973
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2997
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2998
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2999
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3000
    ChildrenCoverage93.nil)))))))))))

theorem compact_parallel93_node_3002 : NodeCoverage93 [14,14,13] 13 52 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3003 : NodeCoverage93 [14,14,12] 12 53 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3004 : NodeCoverage93 [14,14,11] 11 54 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3005 : NodeCoverage93 [14,14,10] 10 55 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3006 : NodeCoverage93 [14,14,9] 9 56 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3007 : NodeCoverage93 [14,14,8] 8 57 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3008 : NodeCoverage93 [14,14,7] 7 58 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3009 : NodeCoverage93 [14,14,6] 6 59 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3010 : NodeCoverage93 [14,14,5] 5 60 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3011 : NodeCoverage93 [14,14,3] 3 62 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3012 : NodeCoverage93 [14,14] 14 65 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3001
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3002
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3003
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3004
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3005
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3006
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3007
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3008
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3009
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3010
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3011
    ChildrenCoverage93.nil)))))))))))

theorem compact_parallel93_node_3013 : NodeCoverage93 [14,13] 13 66 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3014 : NodeCoverage93 [14,12] 12 67 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3015 : NodeCoverage93 [14,11] 11 68 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3016 : NodeCoverage93 [14,10] 10 69 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3017 : NodeCoverage93 [14,9] 9 70 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3018 : NodeCoverage93 [14,8] 8 71 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3019 : NodeCoverage93 [14,7] 7 72 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3020 : NodeCoverage93 [14,6] 6 73 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3021 : NodeCoverage93 [14,5] 5 74 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3022 : NodeCoverage93 [14,3] 3 76 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3023 : NodeCoverage93 [14] 14 79 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3012
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3013
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3014
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3015
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3016
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3017
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3018
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3019
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3020
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3021
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3022
    ChildrenCoverage93.nil)))))))))))

theorem compact_parallel93_node_3024 : NodeCoverage93 [13,13,13,13,13,13,12] 12 3 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3025 : NodeCoverage93 [13,13,13,13,13,13,11] 11 4 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3026 : NodeCoverage93 [13,13,13,13,13,13,10] 10 5 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3027 : NodeCoverage93 [13,13,13,13,13,13,9] 9 6 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3028 : NodeCoverage93 [13,13,13,13,13,13,8] 8 7 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3029 : NodeCoverage93 [13,13,13,13,13,13,7] 7 8 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3030 : NodeCoverage93 [13,13,13,13,13,13,6] 6 9 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3031 : NodeCoverage93 [13,13,13,13,13,13,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3032 : NodeCoverage93 [13,13,13,13,13,13,3] 3 12 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3033 : NodeCoverage93 [13,13,13,13,13,13] 13 15 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3024
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3025
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3026
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3027
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3028
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3029
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3030
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3031
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3032
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_3034 : NodeCoverage93 [13,13,13,13,13,12] 12 16 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3035 : NodeCoverage93 [13,13,13,13,13,11] 11 17 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3036 : NodeCoverage93 [13,13,13,13,13,10] 10 18 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3037 : NodeCoverage93 [13,13,13,13,13,9] 9 19 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3038 : NodeCoverage93 [13,13,13,13,13,8] 8 20 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3039 : NodeCoverage93 [13,13,13,13,13,7] 7 21 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3040 : NodeCoverage93 [13,13,13,13,13,6] 6 22 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3041 : NodeCoverage93 [13,13,13,13,13,5] 5 23 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3042 : NodeCoverage93 [13,13,13,13,13,3] 3 25 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3043 : NodeCoverage93 [13,13,13,13,13] 13 28 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3033
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3034
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3035
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3036
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3037
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3038
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3039
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3040
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3041
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3042
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_3044 : NodeCoverage93 [13,13,13,13,12] 12 29 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3045 : NodeCoverage93 [13,13,13,13,11] 11 30 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3046 : NodeCoverage93 [13,13,13,13,10] 10 31 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3047 : NodeCoverage93 [13,13,13,13,9] 9 32 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3048 : NodeCoverage93 [13,13,13,13,8] 8 33 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3049 : NodeCoverage93 [13,13,13,13,7] 7 34 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3050 : NodeCoverage93 [13,13,13,13,6] 6 35 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3051 : NodeCoverage93 [13,13,13,13,5] 5 36 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3052 : NodeCoverage93 [13,13,13,13,3] 3 38 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3053 : NodeCoverage93 [13,13,13,13] 13 41 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3043
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3044
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3045
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3046
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3047
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3048
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3049
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3050
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3051
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3052
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_3054 : NodeCoverage93 [13,13,13,12] 12 42 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3055 : NodeCoverage93 [13,13,13,11] 11 43 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3056 : NodeCoverage93 [13,13,13,10] 10 44 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3057 : NodeCoverage93 [13,13,13,9] 9 45 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3058 : NodeCoverage93 [13,13,13,8] 8 46 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3059 : NodeCoverage93 [13,13,13,7] 7 47 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3060 : NodeCoverage93 [13,13,13,6] 6 48 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3061 : NodeCoverage93 [13,13,13,5] 5 49 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3062 : NodeCoverage93 [13,13,13,3] 3 51 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3063 : NodeCoverage93 [13,13,13] 13 54 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3053
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3054
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3055
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3056
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3057
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3058
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3059
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3060
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3061
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_3062
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_3064 : NodeCoverage93 [13,13,12] 12 55 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3065 : NodeCoverage93 [13,13,11] 11 56 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_3066 : NodeCoverage93 [13,13,10] 10 57 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
