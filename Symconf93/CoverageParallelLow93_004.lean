module
public import Symconf93.CoverageParallelLow93_003

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2326 : NodeCoverage93 [18,18,18,18,9,9,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_2327 : NodeCoverage93 [18,18,18,18,9,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2326
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2328 : NodeCoverage93 [18,18,18,18,9,8] 8 4 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2329 : NodeCoverage93 [18,18,18,18,9,7] 7 5 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2330 : NodeCoverage93 [18,18,18,18,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2331 : NodeCoverage93 [18,18,18,18,9,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2332 : NodeCoverage93 [18,18,18,18,9,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_2333 : NodeCoverage93 [18,18,18,18,9,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2332
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2334 : NodeCoverage93 [18,18,18,18,9,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2333
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2335 : NodeCoverage93 [18,18,18,18,9,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2334
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2336 : NodeCoverage93 [18,18,18,18,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2327
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2328
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2329
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2330
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2331
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2335
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2337 : NodeCoverage93 [18,18,18,18,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2338 : NodeCoverage93 [18,18,18,18,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2339 : NodeCoverage93 [18,18,18,18,6,6,6,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2340 : NodeCoverage93 [18,18,18,18,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2339
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2341 : NodeCoverage93 [18,18,18,18,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2342 : NodeCoverage93 [18,18,18,18,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2343 : NodeCoverage93 [18,18,18,18,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2342
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2344 : NodeCoverage93 [18,18,18,18,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2343
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2345 : NodeCoverage93 [18,18,18,18,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2340
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2341
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2344
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2346 : NodeCoverage93 [18,18,18,18,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2347 : NodeCoverage93 [18,18,18,18,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2348 : NodeCoverage93 [18,18,18,18,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2347
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2349 : NodeCoverage93 [18,18,18,18,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2348
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2350 : NodeCoverage93 [18,18,18,18,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2349
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2351 : NodeCoverage93 [18,18,18,18,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2350
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2352 : NodeCoverage93 [18,18,18,18,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2345
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2346
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2351
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2353 : NodeCoverage93 [18,18,18,18,5] 5 16 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2354 : NodeCoverage93 [18,18,18,18,3] 3 18 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2355 : NodeCoverage93 [18,18,18,18] 18 21 :=
  node_fork93 (B := [18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2317
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2318
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2319
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2320
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2321
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2322
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2323
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2324
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2325
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2336
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2337
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2338
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2352
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2353
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2354
    ChildrenCoverage93.nil)))))))))))))))

theorem compact_parallel93_node_2356 : NodeCoverage93 [18,18,18,17] 17 22 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2357 : NodeCoverage93 [18,18,18,16] 16 23 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2358 : NodeCoverage93 [18,18,18,15] 15 24 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2359 : NodeCoverage93 [18,18,18,14] 14 25 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2360 : NodeCoverage93 [18,18,18,13] 13 26 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2361 : NodeCoverage93 [18,18,18,12] 12 27 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2362 : NodeCoverage93 [18,18,18,11] 11 28 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2363 : NodeCoverage93 [18,18,18,10] 10 29 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2364 : NodeCoverage93 [18,18,18,9,9,9,9,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2365 : NodeCoverage93 [18,18,18,9,9,9,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2364
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2366 : NodeCoverage93 [18,18,18,9,9,9,8] 8 4 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2367 : NodeCoverage93 [18,18,18,9,9,9,7] 7 5 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2368 : NodeCoverage93 [18,18,18,9,9,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2369 : NodeCoverage93 [18,18,18,9,9,9,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2370 : NodeCoverage93 [18,18,18,9,9,9,3,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2371 : NodeCoverage93 [18,18,18,9,9,9,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2370
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2372 : NodeCoverage93 [18,18,18,9,9,9,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2371
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2373 : NodeCoverage93 [18,18,18,9,9,9,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2372
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2374 : NodeCoverage93 [18,18,18,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2365
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2366
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2367
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2368
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2369
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2373
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2375 : NodeCoverage93 [18,18,18,9,9,8] 8 13 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2376 : NodeCoverage93 [18,18,18,9,9,7] 7 14 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2377 : NodeCoverage93 [18,18,18,9,9,6,6,6,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2378 : NodeCoverage93 [18,18,18,9,9,6,6,6] 6 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2377
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2379 : NodeCoverage93 [18,18,18,9,9,6,6,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2380 : NodeCoverage93 [18,18,18,9,9,6,6,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2381 : NodeCoverage93 [18,18,18,9,9,6,6,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2380
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2382 : NodeCoverage93 [18,18,18,9,9,6,6,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2381
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2383 : NodeCoverage93 [18,18,18,9,9,6,6] 6 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2378
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2379
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2382
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2384 : NodeCoverage93 [18,18,18,9,9,6,5] 5 10 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2385 : NodeCoverage93 [18,18,18,9,9,6,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2386 : NodeCoverage93 [18,18,18,9,9,6,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2385
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2387 : NodeCoverage93 [18,18,18,9,9,6,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2386
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2388 : NodeCoverage93 [18,18,18,9,9,6,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2387
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2389 : NodeCoverage93 [18,18,18,9,9,6,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2388
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2390 : NodeCoverage93 [18,18,18,9,9,6] 6 15 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2383
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2384
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2389
    ChildrenCoverage93.nil)))

end Symconf93
