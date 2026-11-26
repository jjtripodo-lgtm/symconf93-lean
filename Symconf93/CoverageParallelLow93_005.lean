module
public import Symconf93.CoverageParallelLow93_004

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2391 : NodeCoverage93 [18,18,18,9,9,5] 5 16 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2392 : NodeCoverage93 [18,18,18,9,9,3] 3 18 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2393 : NodeCoverage93 [18,18,18,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2374
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2375
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2376
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2390
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2391
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2392
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2394 : NodeCoverage93 [18,18,18,9,8] 8 22 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2395 : NodeCoverage93 [18,18,18,9,7] 7 23 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2396 : NodeCoverage93 [18,18,18,9,6,6,6,6,6] 6 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2397 : NodeCoverage93 [18,18,18,9,6,6,6,6,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2398 : NodeCoverage93 [18,18,18,9,6,6,6,6,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2397
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2399 : NodeCoverage93 [18,18,18,9,6,6,6,6] 6 6 :=
  node_fork93 (B := [6,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2396
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2398
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_2400 : NodeCoverage93 [18,18,18,9,6,6,6,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2401 : NodeCoverage93 [18,18,18,9,6,6,6,3,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2402 : NodeCoverage93 [18,18,18,9,6,6,6,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2401
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2403 : NodeCoverage93 [18,18,18,9,6,6,6,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2402
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2404 : NodeCoverage93 [18,18,18,9,6,6,6,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2403
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2405 : NodeCoverage93 [18,18,18,9,6,6,6] 6 12 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2399
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2400
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2404
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2406 : NodeCoverage93 [18,18,18,9,6,6,5] 5 13 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2407 : NodeCoverage93 [18,18,18,9,6,6,3,3,3,3,3,3] 3 0 :=
  node_no_weak_demand93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2408 : NodeCoverage93 [18,18,18,9,6,6,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2407
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2409 : NodeCoverage93 [18,18,18,9,6,6,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2408
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2410 : NodeCoverage93 [18,18,18,9,6,6,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2409
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2411 : NodeCoverage93 [18,18,18,9,6,6,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2410
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2412 : NodeCoverage93 [18,18,18,9,6,6,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2411
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_2413 : NodeCoverage93 [18,18,18,9,6,6] 6 18 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2405
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2406
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2412
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2414 : NodeCoverage93 [18,18,18,9,6,5] 5 19 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2415 : NodeCoverage93 [18,18,18,9,6,3] 3 21 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2416 : NodeCoverage93 [18,18,18,9,6] 6 24 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2413
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2414
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2415
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2417 : NodeCoverage93 [18,18,18,9,5] 5 25 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2418 : NodeCoverage93 [18,18,18,9,3] 3 27 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2419 : NodeCoverage93 [18,18,18,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2393
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2394
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2395
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2416
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2417
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2418
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2420 : NodeCoverage93 [18,18,18,8] 8 31 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2421 : NodeCoverage93 [18,18,18,7] 7 32 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2422 : NodeCoverage93 [18,18,18,6] 6 33 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2423 : NodeCoverage93 [18,18,18,5] 5 34 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2424 : NodeCoverage93 [18,18,18,3] 3 36 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2425 : NodeCoverage93 [18,18,18] 18 39 :=
  node_fork93 (B := [18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2355
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2356
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2357
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2358
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2359
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2360
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2361
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2362
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2363
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2419
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2420
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2421
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2422
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2423
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2424
    ChildrenCoverage93.nil)))))))))))))))

theorem compact_parallel93_node_2426 : NodeCoverage93 [18,18,17] 17 40 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2427 : NodeCoverage93 [18,18,16] 16 41 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
