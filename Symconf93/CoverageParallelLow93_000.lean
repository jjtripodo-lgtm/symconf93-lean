module
public import Symconf93.AllDemandBanks93

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2051 : NodeCoverage93 [20,20,20,20,13] 13 0 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2052 : NodeCoverage93 [20,20,20,20,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2053 : NodeCoverage93 [20,20,20,20,9] 9 4 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2054 : NodeCoverage93 [20,20,20,20,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2055 : NodeCoverage93 [20,20,20,20,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2056 : NodeCoverage93 [20,20,20,20,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2057 : NodeCoverage93 [20,20,20,20,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2058 : NodeCoverage93 [20,20,20,20,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2057
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2059 : NodeCoverage93 [20,20,20,20,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2060 : NodeCoverage93 [20,20,20,20,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2058
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2059
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2061 : NodeCoverage93 [20,20,20,20,3] 3 10 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2062 : NodeCoverage93 [20,20,20,20] 20 13 :=
  node_fork93 (B := [13,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2051
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2052
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2053
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2054
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2055
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2056
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2060
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2061
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_2063 : NodeCoverage93 [20,20,20,19] 19 14 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2064 : NodeCoverage93 [20,20,20,18] 18 15 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2065 : NodeCoverage93 [20,20,20,17] 17 16 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2066 : NodeCoverage93 [20,20,20,16] 16 17 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2067 : NodeCoverage93 [20,20,20,15] 15 18 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2068 : NodeCoverage93 [20,20,20,14] 14 19 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2069 : NodeCoverage93 [20,20,20,13] 13 20 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2070 : NodeCoverage93 [20,20,20,12] 12 21 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2071 : NodeCoverage93 [20,20,20,11] 11 22 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2072 : NodeCoverage93 [20,20,20,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2073 : NodeCoverage93 [20,20,20,10,10,9] 9 4 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2074 : NodeCoverage93 [20,20,20,10,10,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2075 : NodeCoverage93 [20,20,20,10,10,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2076 : NodeCoverage93 [20,20,20,10,10,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2077 : NodeCoverage93 [20,20,20,10,10,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2078 : NodeCoverage93 [20,20,20,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2077
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2079 : NodeCoverage93 [20,20,20,10,10,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2080 : NodeCoverage93 [20,20,20,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2078
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2079
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2081 : NodeCoverage93 [20,20,20,10,10,3] 3 10 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2082 : NodeCoverage93 [20,20,20,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2072
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2073
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2074
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2075
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2076
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2080
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2081
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2083 : NodeCoverage93 [20,20,20,10,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2084 : NodeCoverage93 [20,20,20,10,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2085 : NodeCoverage93 [20,20,20,10,7] 7 16 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2086 : NodeCoverage93 [20,20,20,10,6] 6 17 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2087 : NodeCoverage93 [20,20,20,10,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2088 : NodeCoverage93 [20,20,20,10,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2087
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2089 : NodeCoverage93 [20,20,20,10,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2090 : NodeCoverage93 [20,20,20,10,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2088
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2089
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2091 : NodeCoverage93 [20,20,20,10,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2092 : NodeCoverage93 [20,20,20,10,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2090
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2091
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2093 : NodeCoverage93 [20,20,20,10,5,3] 3 15 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2094 : NodeCoverage93 [20,20,20,10,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2092
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2093
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2095 : NodeCoverage93 [20,20,20,10,3] 3 20 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2096 : NodeCoverage93 [20,20,20,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2082
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2083
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2084
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2085
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2086
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2094
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2095
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2097 : NodeCoverage93 [20,20,20,9] 9 24 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2098 : NodeCoverage93 [20,20,20,8] 8 25 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2099 : NodeCoverage93 [20,20,20,7] 7 26 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2100 : NodeCoverage93 [20,20,20,6] 6 27 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2101 : NodeCoverage93 [20,20,20,5] 5 28 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2102 : NodeCoverage93 [20,20,20,3] 3 30 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2103 : NodeCoverage93 [20,20,20] 20 33 :=
  node_fork93 (B := [20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2062
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2063
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2064
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2065
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2066
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2067
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2068
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2069
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2070
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2071
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2096
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2097
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2098
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2099
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2100
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2101
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2102
    ChildrenCoverage93.nil)))))))))))))))))

theorem compact_parallel93_node_2104 : NodeCoverage93 [20,20,19] 19 34 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2105 : NodeCoverage93 [20,20,18] 18 35 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2106 : NodeCoverage93 [20,20,17] 17 36 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2107 : NodeCoverage93 [20,20,16] 16 37 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2108 : NodeCoverage93 [20,20,15] 15 38 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2109 : NodeCoverage93 [20,20,14] 14 39 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2110 : NodeCoverage93 [20,20,13] 13 40 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2111 : NodeCoverage93 [20,20,12] 12 41 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2112 : NodeCoverage93 [20,20,11] 11 42 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2113 : NodeCoverage93 [20,20,10,10,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2114 : NodeCoverage93 [20,20,10,10,10,10,9] 9 4 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2115 : NodeCoverage93 [20,20,10,10,10,10,8] 8 5 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2116 : NodeCoverage93 [20,20,10,10,10,10,7] 7 6 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2117 : NodeCoverage93 [20,20,10,10,10,10,6] 6 7 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
