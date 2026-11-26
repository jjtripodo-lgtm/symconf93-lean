module
public import Symconf93.CoverageParallelLow93_001

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2183 : NodeCoverage93 [20,12,5] 5 56 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2184 : NodeCoverage93 [20,12,3] 3 58 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2185 : NodeCoverage93 [20,12] 12 61 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2176
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2177
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2178
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2179
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2180
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2181
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2182
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2183
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2184
    ChildrenCoverage93.nil)))))))))

theorem compact_parallel93_node_2186 : NodeCoverage93 [20,11,11] 11 51 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2187 : NodeCoverage93 [20,11,10] 10 52 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2188 : NodeCoverage93 [20,11,9] 9 53 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2189 : NodeCoverage93 [20,11,8] 8 54 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2190 : NodeCoverage93 [20,11,7] 7 55 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2191 : NodeCoverage93 [20,11,6] 6 56 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2192 : NodeCoverage93 [20,11,5] 5 57 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2193 : NodeCoverage93 [20,11,3] 3 59 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2194 : NodeCoverage93 [20,11] 11 62 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2186
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2187
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2188
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2189
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2190
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2191
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2192
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2193
    ChildrenCoverage93.nil))))))))

theorem compact_parallel93_node_2195 : NodeCoverage93 [20,10,10,10,10,10,10,10] 10 3 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2196 : NodeCoverage93 [20,10,10,10,10,10,10,9] 9 4 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2197 : NodeCoverage93 [20,10,10,10,10,10,10,8] 8 5 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2198 : NodeCoverage93 [20,10,10,10,10,10,10,7] 7 6 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2199 : NodeCoverage93 [20,10,10,10,10,10,10,6] 6 7 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2200 : NodeCoverage93 [20,10,10,10,10,10,10,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2201 : NodeCoverage93 [20,10,10,10,10,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2200
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2202 : NodeCoverage93 [20,10,10,10,10,10,10,5,3] 3 5 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2203 : NodeCoverage93 [20,10,10,10,10,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2201
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2202
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2204 : NodeCoverage93 [20,10,10,10,10,10,10,3] 3 10 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2205 : NodeCoverage93 [20,10,10,10,10,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2195
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2196
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2197
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2198
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2199
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2203
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2204
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2206 : NodeCoverage93 [20,10,10,10,10,10,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2207 : NodeCoverage93 [20,10,10,10,10,10,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2208 : NodeCoverage93 [20,10,10,10,10,10,7] 7 16 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2209 : NodeCoverage93 [20,10,10,10,10,10,6] 6 17 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2210 : NodeCoverage93 [20,10,10,10,10,10,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2211 : NodeCoverage93 [20,10,10,10,10,10,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2210
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2212 : NodeCoverage93 [20,10,10,10,10,10,5,5,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2213 : NodeCoverage93 [20,10,10,10,10,10,5,5,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2211
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2212
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2214 : NodeCoverage93 [20,10,10,10,10,10,5,5,3] 3 10 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2215 : NodeCoverage93 [20,10,10,10,10,10,5,5] 5 13 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2213
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2214
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2216 : NodeCoverage93 [20,10,10,10,10,10,5,3] 3 15 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2217 : NodeCoverage93 [20,10,10,10,10,10,5] 5 18 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2215
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2216
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2218 : NodeCoverage93 [20,10,10,10,10,10,3] 3 20 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2219 : NodeCoverage93 [20,10,10,10,10,10] 10 23 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2205
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2206
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2207
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2208
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2209
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2217
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2218
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2220 : NodeCoverage93 [20,10,10,10,10,9] 9 24 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2221 : NodeCoverage93 [20,10,10,10,10,8] 8 25 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2222 : NodeCoverage93 [20,10,10,10,10,7] 7 26 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2223 : NodeCoverage93 [20,10,10,10,10,6] 6 27 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2224 : NodeCoverage93 [20,10,10,10,10,5] 5 28 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2225 : NodeCoverage93 [20,10,10,10,10,3] 3 30 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2226 : NodeCoverage93 [20,10,10,10,10] 10 33 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2219
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2220
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2221
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2222
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2223
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2224
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2225
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2227 : NodeCoverage93 [20,10,10,10,9] 9 34 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2228 : NodeCoverage93 [20,10,10,10,8] 8 35 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2229 : NodeCoverage93 [20,10,10,10,7] 7 36 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2230 : NodeCoverage93 [20,10,10,10,6] 6 37 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2231 : NodeCoverage93 [20,10,10,10,5] 5 38 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2232 : NodeCoverage93 [20,10,10,10,3] 3 40 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2233 : NodeCoverage93 [20,10,10,10] 10 43 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2226
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2227
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2228
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2229
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2230
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2231
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2232
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2234 : NodeCoverage93 [20,10,10,9] 9 44 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2235 : NodeCoverage93 [20,10,10,8] 8 45 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2236 : NodeCoverage93 [20,10,10,7] 7 46 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2237 : NodeCoverage93 [20,10,10,6] 6 47 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2238 : NodeCoverage93 [20,10,10,5] 5 48 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2239 : NodeCoverage93 [20,10,10,3] 3 50 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2240 : NodeCoverage93 [20,10,10] 10 53 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2233
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2234
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2235
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2236
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2237
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2238
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2239
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2241 : NodeCoverage93 [20,10,9] 9 54 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2242 : NodeCoverage93 [20,10,8] 8 55 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2243 : NodeCoverage93 [20,10,7] 7 56 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2244 : NodeCoverage93 [20,10,6] 6 57 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2245 : NodeCoverage93 [20,10,5] 5 58 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2246 : NodeCoverage93 [20,10,3] 3 60 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2247 : NodeCoverage93 [20,10] 10 63 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2240
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2241
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2242
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2243
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2244
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2245
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2246
    ChildrenCoverage93.nil)))))))

theorem compact_parallel93_node_2248 : NodeCoverage93 [20,9] 9 64 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2249 : NodeCoverage93 [20,8] 8 65 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2250 : NodeCoverage93 [20,7] 7 66 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
