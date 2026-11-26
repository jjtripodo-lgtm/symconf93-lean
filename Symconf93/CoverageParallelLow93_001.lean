module
public import Symconf93.CoverageParallelLow93_000

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2118 : NodeCoverage93 [20,20,10,10,10,10,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2119 : NodeCoverage93 [20,20,10,10,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2118
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2120 : NodeCoverage93 [20,20,10,10,10,10,5,3] 3 5 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2121 : NodeCoverage93 [20,20,10,10,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2119
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2120
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2122 : NodeCoverage93 [20,20,10,10,10,10,3] 3 10 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2123 : NodeCoverage93 [20,20,10,10,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2113
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2114
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2115
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2116
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2117
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2121
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2122
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2124 : NodeCoverage93 [20,20,10,10,10,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2125 : NodeCoverage93 [20,20,10,10,10,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2126 : NodeCoverage93 [20,20,10,10,10,7] 7 16 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2127 : NodeCoverage93 [20,20,10,10,10,6] 6 17 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2128 : NodeCoverage93 [20,20,10,10,10,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2129 : NodeCoverage93 [20,20,10,10,10,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2128
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2130 : NodeCoverage93 [20,20,10,10,10,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2131 : NodeCoverage93 [20,20,10,10,10,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2129
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2130
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2132 : NodeCoverage93 [20,20,10,10,10,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2133 : NodeCoverage93 [20,20,10,10,10,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2131
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2132
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2134 : NodeCoverage93 [20,20,10,10,10,5,3] 3 15 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2135 : NodeCoverage93 [20,20,10,10,10,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2133
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2134
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2136 : NodeCoverage93 [20,20,10,10,10,3] 3 20 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2137 : NodeCoverage93 [20,20,10,10,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2123
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2124
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2125
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2126
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2127
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2135
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2136
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2138 : NodeCoverage93 [20,20,10,10,9] 9 24 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2139 : NodeCoverage93 [20,20,10,10,8] 8 25 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2140 : NodeCoverage93 [20,20,10,10,7] 7 26 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2141 : NodeCoverage93 [20,20,10,10,6] 6 27 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2142 : NodeCoverage93 [20,20,10,10,5] 5 28 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2143 : NodeCoverage93 [20,20,10,10,3] 3 30 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2144 : NodeCoverage93 [20,20,10,10] 10 33 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2137
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2138
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2139
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2140
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2141
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2142
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2143
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2145 : NodeCoverage93 [20,20,10,9] 9 34 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2146 : NodeCoverage93 [20,20,10,8] 8 35 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2147 : NodeCoverage93 [20,20,10,7] 7 36 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2148 : NodeCoverage93 [20,20,10,6] 6 37 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2149 : NodeCoverage93 [20,20,10,5] 5 38 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2150 : NodeCoverage93 [20,20,10,3] 3 40 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2151 : NodeCoverage93 [20,20,10] 10 43 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2144
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2145
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2146
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2147
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2148
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2149
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2150
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2152 : NodeCoverage93 [20,20,9] 9 44 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2153 : NodeCoverage93 [20,20,8] 8 45 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2154 : NodeCoverage93 [20,20,7] 7 46 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2155 : NodeCoverage93 [20,20,6] 6 47 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2156 : NodeCoverage93 [20,20,5] 5 48 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2157 : NodeCoverage93 [20,20,3] 3 50 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2158 : NodeCoverage93 [20,20] 20 53 :=
  node_fork93 (B := [20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2103
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2104
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2105
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2106
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2107
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2108
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2109
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2110
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2111
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2112
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2151
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2152
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2153
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2154
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2155
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2156
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2157
    ChildrenCoverage93.nil)))))))))))))))))

theorem compact_parallel93_node_2159 : NodeCoverage93 [20,19] 19 54 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2160 : NodeCoverage93 [20,18] 18 55 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2161 : NodeCoverage93 [20,17] 17 56 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2162 : NodeCoverage93 [20,16] 16 57 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2163 : NodeCoverage93 [20,15] 15 58 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2164 : NodeCoverage93 [20,14] 14 59 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2165 : NodeCoverage93 [20,13,13] 13 47 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2166 : NodeCoverage93 [20,13,12] 12 48 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2167 : NodeCoverage93 [20,13,11] 11 49 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2168 : NodeCoverage93 [20,13,10] 10 50 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2169 : NodeCoverage93 [20,13,9] 9 51 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2170 : NodeCoverage93 [20,13,8] 8 52 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2171 : NodeCoverage93 [20,13,7] 7 53 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2172 : NodeCoverage93 [20,13,6] 6 54 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2173 : NodeCoverage93 [20,13,5] 5 55 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2174 : NodeCoverage93 [20,13,3] 3 57 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2175 : NodeCoverage93 [20,13] 13 60 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2165
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2166
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2167
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2168
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2169
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2170
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2171
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2172
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2173
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2174
    ChildrenCoverage93.nil))))))))))

theorem compact_parallel93_node_2176 : NodeCoverage93 [20,12,12] 12 49 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2177 : NodeCoverage93 [20,12,11] 11 50 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2178 : NodeCoverage93 [20,12,10] 10 51 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2179 : NodeCoverage93 [20,12,9] 9 52 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2180 : NodeCoverage93 [20,12,8] 8 53 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2181 : NodeCoverage93 [20,12,7] 7 54 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2182 : NodeCoverage93 [20,12,6] 6 55 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
