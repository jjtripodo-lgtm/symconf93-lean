module
public import Symconf93.CoverageParallelLow93_002

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2251 : NodeCoverage93 [20,6] 6 67 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2252 : NodeCoverage93 [20,5] 5 68 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2253 : NodeCoverage93 [20,3] 3 70 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2254 : NodeCoverage93 [20] 20 73 :=
  node_fork93 (B := [20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2158
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2159
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2160
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2161
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2162
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2163
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2164
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2175
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2185
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2194
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2247
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2248
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2249
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2250
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2251
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2252
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2253
    ChildrenCoverage93.nil)))))))))))))))))

theorem compact_parallel93_node_2255 : NodeCoverage93 [19,19,19,19,17] 17 0 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2256 : NodeCoverage93 [19,19,19,19,14] 14 3 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2257 : NodeCoverage93 [19,19,19,19,13] 13 4 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2258 : NodeCoverage93 [19,19,19,19,12] 12 5 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2259 : NodeCoverage93 [19,19,19,19,11] 11 6 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2260 : NodeCoverage93 [19,19,19,19,10] 10 7 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2261 : NodeCoverage93 [19,19,19,19,9] 9 8 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2262 : NodeCoverage93 [19,19,19,19,8] 8 9 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2263 : NodeCoverage93 [19,19,19,19,7] 7 10 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2264 : NodeCoverage93 [19,19,19,19,6] 6 11 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2265 : NodeCoverage93 [19,19,19,19,5] 5 12 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2266 : NodeCoverage93 [19,19,19,19,3] 3 14 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2267 : NodeCoverage93 [19,19,19,19] 19 17 :=
  node_fork93 (B := [17,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2255
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2256
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2257
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2258
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2259
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2260
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2261
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2262
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2263
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2264
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2265
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2266
    ChildrenCoverage93.nil))))))))))))

theorem compact_parallel93_node_2268 : NodeCoverage93 [19,19,19,18] 18 18 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2269 : NodeCoverage93 [19,19,19,17] 17 19 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2270 : NodeCoverage93 [19,19,19,16] 16 20 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2271 : NodeCoverage93 [19,19,19,15] 15 21 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2272 : NodeCoverage93 [19,19,19,14] 14 22 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2273 : NodeCoverage93 [19,19,19,13] 13 23 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2274 : NodeCoverage93 [19,19,19,12] 12 24 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2275 : NodeCoverage93 [19,19,19,11] 11 25 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2276 : NodeCoverage93 [19,19,19,10] 10 26 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2277 : NodeCoverage93 [19,19,19,9] 9 27 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2278 : NodeCoverage93 [19,19,19,8] 8 28 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2279 : NodeCoverage93 [19,19,19,7] 7 29 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2280 : NodeCoverage93 [19,19,19,6] 6 30 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2281 : NodeCoverage93 [19,19,19,5] 5 31 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2282 : NodeCoverage93 [19,19,19,3] 3 33 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2283 : NodeCoverage93 [19,19,19] 19 36 :=
  node_fork93 (B := [19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2267
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2268
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2269
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2270
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2271
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2272
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2273
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2274
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2275
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2276
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2277
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2278
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2279
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2280
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2281
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2282
    ChildrenCoverage93.nil))))))))))))))))

theorem compact_parallel93_node_2284 : NodeCoverage93 [19,19,18] 18 37 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2285 : NodeCoverage93 [19,19,17] 17 38 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2286 : NodeCoverage93 [19,19,16] 16 39 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2287 : NodeCoverage93 [19,19,15] 15 40 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2288 : NodeCoverage93 [19,19,14] 14 41 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2289 : NodeCoverage93 [19,19,13] 13 42 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2290 : NodeCoverage93 [19,19,12] 12 43 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2291 : NodeCoverage93 [19,19,11] 11 44 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2292 : NodeCoverage93 [19,19,10] 10 45 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2293 : NodeCoverage93 [19,19,9] 9 46 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2294 : NodeCoverage93 [19,19,8] 8 47 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2295 : NodeCoverage93 [19,19,7] 7 48 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2296 : NodeCoverage93 [19,19,6] 6 49 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2297 : NodeCoverage93 [19,19,5] 5 50 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2298 : NodeCoverage93 [19,19,3] 3 52 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2299 : NodeCoverage93 [19,19] 19 55 :=
  node_fork93 (B := [19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2283
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2284
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2285
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2286
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2287
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2288
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2289
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2290
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2291
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2292
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2293
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2294
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2295
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2296
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2297
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2298
    ChildrenCoverage93.nil))))))))))))))))

theorem compact_parallel93_node_2300 : NodeCoverage93 [19,18] 18 56 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2301 : NodeCoverage93 [19,17] 17 57 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2302 : NodeCoverage93 [19,16] 16 58 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2303 : NodeCoverage93 [19,15] 15 59 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2304 : NodeCoverage93 [19,14] 14 60 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2305 : NodeCoverage93 [19,13] 13 61 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2306 : NodeCoverage93 [19,12] 12 62 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2307 : NodeCoverage93 [19,11] 11 63 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2308 : NodeCoverage93 [19,10] 10 64 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2309 : NodeCoverage93 [19,9] 9 65 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2310 : NodeCoverage93 [19,8] 8 66 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2311 : NodeCoverage93 [19,7] 7 67 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2312 : NodeCoverage93 [19,6] 6 68 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2313 : NodeCoverage93 [19,5] 5 69 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2314 : NodeCoverage93 [19,3] 3 71 :=
  demand_node_prune93 19 compact93_demands_19 compact93_demands_19_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2315 : NodeCoverage93 [19] 19 74 :=
  node_fork93 (B := [19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2299
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2300
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2301
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2302
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2303
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2304
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2305
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2306
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2307
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2308
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2309
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2310
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2311
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2312
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2313
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2314
    ChildrenCoverage93.nil))))))))))))))))

theorem compact_parallel93_node_2316 : NodeCoverage93 [18,18,18,18,18,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2317 : NodeCoverage93 [18,18,18,18,18] 18 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2316
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2318 : NodeCoverage93 [18,18,18,18,17] 17 4 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2319 : NodeCoverage93 [18,18,18,18,16] 16 5 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2320 : NodeCoverage93 [18,18,18,18,15] 15 6 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2321 : NodeCoverage93 [18,18,18,18,14] 14 7 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2322 : NodeCoverage93 [18,18,18,18,13] 13 8 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2323 : NodeCoverage93 [18,18,18,18,12] 12 9 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2324 : NodeCoverage93 [18,18,18,18,11] 11 10 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2325 : NodeCoverage93 [18,18,18,18,10] 10 11 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
