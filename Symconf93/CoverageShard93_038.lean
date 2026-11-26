module
public import Symconf93.CoverageShard93_037

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1310 : NodeCoverage93 [28,12] 12 53 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1311 : NodeCoverage93 [28,11] 11 54 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1312 : NodeCoverage93 [28,10] 10 55 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1313 : NodeCoverage93 [28,9] 9 56 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1314 : NodeCoverage93 [28,8] 8 57 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1315 : NodeCoverage93 [28,7] 7 58 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1316 : NodeCoverage93 [28,6] 6 59 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1317 : NodeCoverage93 [28,5] 5 60 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1318 : NodeCoverage93 [28,3] 3 62 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1319 : NodeCoverage93 [28] 28 65 :=
  node_fork93 (B := [28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1260
    (ChildrenCoverage93.cons _ _ compact93_node_1261
    (ChildrenCoverage93.cons _ _ compact93_node_1262
    (ChildrenCoverage93.cons _ _ compact93_node_1263
    (ChildrenCoverage93.cons _ _ compact93_node_1264
    (ChildrenCoverage93.cons _ _ compact93_node_1265
    (ChildrenCoverage93.cons _ _ compact93_node_1266
    (ChildrenCoverage93.cons _ _ compact93_node_1267
    (ChildrenCoverage93.cons _ _ compact93_node_1268
    (ChildrenCoverage93.cons _ _ compact93_node_1269
    (ChildrenCoverage93.cons _ _ compact93_node_1270
    (ChildrenCoverage93.cons _ _ compact93_node_1271
    (ChildrenCoverage93.cons _ _ compact93_node_1272
    (ChildrenCoverage93.cons _ _ compact93_node_1273
    (ChildrenCoverage93.cons _ _ compact93_node_1308
    (ChildrenCoverage93.cons _ _ compact93_node_1309
    (ChildrenCoverage93.cons _ _ compact93_node_1310
    (ChildrenCoverage93.cons _ _ compact93_node_1311
    (ChildrenCoverage93.cons _ _ compact93_node_1312
    (ChildrenCoverage93.cons _ _ compact93_node_1313
    (ChildrenCoverage93.cons _ _ compact93_node_1314
    (ChildrenCoverage93.cons _ _ compact93_node_1315
    (ChildrenCoverage93.cons _ _ compact93_node_1316
    (ChildrenCoverage93.cons _ _ compact93_node_1317
    (ChildrenCoverage93.cons _ _ compact93_node_1318
    ChildrenCoverage93.nil)))))))))))))))))))))))))

theorem compact93_node_1320 : NodeCoverage93 [27,27,27,12] 12 0 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1321 : NodeCoverage93 [27,27,27,9,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_1322 : NodeCoverage93 [27,27,27,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1321
    ChildrenCoverage93.nil)

theorem compact93_node_1323 : NodeCoverage93 [27,27,27,8] 8 4 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1324 : NodeCoverage93 [27,27,27,7] 7 5 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1325 : NodeCoverage93 [27,27,27,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1326 : NodeCoverage93 [27,27,27,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1327 : NodeCoverage93 [27,27,27,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_1328 : NodeCoverage93 [27,27,27,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1327
    ChildrenCoverage93.nil)

theorem compact93_node_1329 : NodeCoverage93 [27,27,27,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1328
    ChildrenCoverage93.nil)

theorem compact93_node_1330 : NodeCoverage93 [27,27,27,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1329
    ChildrenCoverage93.nil)

theorem compact93_node_1331 : NodeCoverage93 [27,27,27] 27 12 :=
  node_fork93 (B := [12,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1320
    (ChildrenCoverage93.cons _ _ compact93_node_1322
    (ChildrenCoverage93.cons _ _ compact93_node_1323
    (ChildrenCoverage93.cons _ _ compact93_node_1324
    (ChildrenCoverage93.cons _ _ compact93_node_1325
    (ChildrenCoverage93.cons _ _ compact93_node_1326
    (ChildrenCoverage93.cons _ _ compact93_node_1330
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1332 : NodeCoverage93 [27,27,26] 26 13 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1333 : NodeCoverage93 [27,27,25] 25 14 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1334 : NodeCoverage93 [27,27,24] 24 15 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1335 : NodeCoverage93 [27,27,23] 23 16 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1336 : NodeCoverage93 [27,27,22] 22 17 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1337 : NodeCoverage93 [27,27,21] 21 18 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1338 : NodeCoverage93 [27,27,20] 20 19 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1339 : NodeCoverage93 [27,27,19] 19 20 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1340 : NodeCoverage93 [27,27,18] 18 21 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1341 : NodeCoverage93 [27,27,17] 17 22 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1342 : NodeCoverage93 [27,27,16] 16 23 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1343 : NodeCoverage93 [27,27,15] 15 24 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1344 : NodeCoverage93 [27,27,14] 14 25 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1345 : NodeCoverage93 [27,27,13] 13 26 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1346 : NodeCoverage93 [27,27,12] 12 27 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1347 : NodeCoverage93 [27,27,11] 11 28 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1348 : NodeCoverage93 [27,27,10] 10 29 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1349 : NodeCoverage93 [27,27,9,9,9,9,3] 3 0 :=
  node_no_weak_demand93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1350 : NodeCoverage93 [27,27,9,9,9,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1349
    ChildrenCoverage93.nil)

theorem compact93_node_1351 : NodeCoverage93 [27,27,9,9,9,8] 8 4 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1352 : NodeCoverage93 [27,27,9,9,9,7] 7 5 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1353 : NodeCoverage93 [27,27,9,9,9,6] 6 6 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1354 : NodeCoverage93 [27,27,9,9,9,5] 5 7 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1355 : NodeCoverage93 [27,27,9,9,9,3,3,3,3] 3 0 :=
  node_no_weak_demand93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1356 : NodeCoverage93 [27,27,9,9,9,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1355
    ChildrenCoverage93.nil)

theorem compact93_node_1357 : NodeCoverage93 [27,27,9,9,9,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1356
    ChildrenCoverage93.nil)

theorem compact93_node_1358 : NodeCoverage93 [27,27,9,9,9,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1357
    ChildrenCoverage93.nil)

theorem compact93_node_1359 : NodeCoverage93 [27,27,9,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1350
    (ChildrenCoverage93.cons _ _ compact93_node_1351
    (ChildrenCoverage93.cons _ _ compact93_node_1352
    (ChildrenCoverage93.cons _ _ compact93_node_1353
    (ChildrenCoverage93.cons _ _ compact93_node_1354
    (ChildrenCoverage93.cons _ _ compact93_node_1358
    ChildrenCoverage93.nil))))))

theorem compact93_node_1360 : NodeCoverage93 [27,27,9,9,8] 8 13 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1361 : NodeCoverage93 [27,27,9,9,7] 7 14 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1362 : NodeCoverage93 [27,27,9,9,6] 6 15 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1363 : NodeCoverage93 [27,27,9,9,5] 5 16 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1364 : NodeCoverage93 [27,27,9,9,3] 3 18 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1365 : NodeCoverage93 [27,27,9,9] 9 21 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1359
    (ChildrenCoverage93.cons _ _ compact93_node_1360
    (ChildrenCoverage93.cons _ _ compact93_node_1361
    (ChildrenCoverage93.cons _ _ compact93_node_1362
    (ChildrenCoverage93.cons _ _ compact93_node_1363
    (ChildrenCoverage93.cons _ _ compact93_node_1364
    ChildrenCoverage93.nil))))))

theorem compact93_node_1366 : NodeCoverage93 [27,27,9,8] 8 22 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1367 : NodeCoverage93 [27,27,9,7] 7 23 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1368 : NodeCoverage93 [27,27,9,6] 6 24 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1369 : NodeCoverage93 [27,27,9,5] 5 25 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1370 : NodeCoverage93 [27,27,9,3] 3 27 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1371 : NodeCoverage93 [27,27,9] 9 30 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1365
    (ChildrenCoverage93.cons _ _ compact93_node_1366
    (ChildrenCoverage93.cons _ _ compact93_node_1367
    (ChildrenCoverage93.cons _ _ compact93_node_1368
    (ChildrenCoverage93.cons _ _ compact93_node_1369
    (ChildrenCoverage93.cons _ _ compact93_node_1370
    ChildrenCoverage93.nil))))))

theorem compact93_node_1372 : NodeCoverage93 [27,27,8] 8 31 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1373 : NodeCoverage93 [27,27,7] 7 32 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1374 : NodeCoverage93 [27,27,6] 6 33 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1375 : NodeCoverage93 [27,27,5] 5 34 :=
  demand_node_prune93 27 compact93_demands_27 compact93_demands_27_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
