module
public import Symconf93.CoverageShard93_036

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1235 : NodeCoverage93 [28,28,14,10] 10 13 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1236 : NodeCoverage93 [28,28,14,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1237 : NodeCoverage93 [28,28,14,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1238 : NodeCoverage93 [28,28,14,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1239 : NodeCoverage93 [28,28,14,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1240 : NodeCoverage93 [28,28,14,7,7,3] 3 6 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1241 : NodeCoverage93 [28,28,14,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1238
    (ChildrenCoverage93.cons _ _ compact93_node_1239
    (ChildrenCoverage93.cons _ _ compact93_node_1240
    ChildrenCoverage93.nil)))

theorem compact93_node_1242 : NodeCoverage93 [28,28,14,7,6] 6 10 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1243 : NodeCoverage93 [28,28,14,7,5] 5 11 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1244 : NodeCoverage93 [28,28,14,7,3] 3 13 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1245 : NodeCoverage93 [28,28,14,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1241
    (ChildrenCoverage93.cons _ _ compact93_node_1242
    (ChildrenCoverage93.cons _ _ compact93_node_1243
    (ChildrenCoverage93.cons _ _ compact93_node_1244
    ChildrenCoverage93.nil))))

theorem compact93_node_1246 : NodeCoverage93 [28,28,14,6] 6 17 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1247 : NodeCoverage93 [28,28,14,5] 5 18 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1248 : NodeCoverage93 [28,28,14,3] 3 20 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1249 : NodeCoverage93 [28,28,14] 14 23 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1231
    (ChildrenCoverage93.cons _ _ compact93_node_1232
    (ChildrenCoverage93.cons _ _ compact93_node_1233
    (ChildrenCoverage93.cons _ _ compact93_node_1234
    (ChildrenCoverage93.cons _ _ compact93_node_1235
    (ChildrenCoverage93.cons _ _ compact93_node_1236
    (ChildrenCoverage93.cons _ _ compact93_node_1237
    (ChildrenCoverage93.cons _ _ compact93_node_1245
    (ChildrenCoverage93.cons _ _ compact93_node_1246
    (ChildrenCoverage93.cons _ _ compact93_node_1247
    (ChildrenCoverage93.cons _ _ compact93_node_1248
    ChildrenCoverage93.nil)))))))))))

theorem compact93_node_1250 : NodeCoverage93 [28,28,13] 13 24 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1251 : NodeCoverage93 [28,28,12] 12 25 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1252 : NodeCoverage93 [28,28,11] 11 26 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1253 : NodeCoverage93 [28,28,10] 10 27 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1254 : NodeCoverage93 [28,28,9] 9 28 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1255 : NodeCoverage93 [28,28,8] 8 29 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1256 : NodeCoverage93 [28,28,7] 7 30 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1257 : NodeCoverage93 [28,28,6] 6 31 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1258 : NodeCoverage93 [28,28,5] 5 32 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1259 : NodeCoverage93 [28,28,3] 3 34 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1260 : NodeCoverage93 [28,28] 28 37 :=
  node_fork93 (B := [28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1217
    (ChildrenCoverage93.cons _ _ compact93_node_1218
    (ChildrenCoverage93.cons _ _ compact93_node_1219
    (ChildrenCoverage93.cons _ _ compact93_node_1220
    (ChildrenCoverage93.cons _ _ compact93_node_1221
    (ChildrenCoverage93.cons _ _ compact93_node_1222
    (ChildrenCoverage93.cons _ _ compact93_node_1223
    (ChildrenCoverage93.cons _ _ compact93_node_1224
    (ChildrenCoverage93.cons _ _ compact93_node_1225
    (ChildrenCoverage93.cons _ _ compact93_node_1226
    (ChildrenCoverage93.cons _ _ compact93_node_1227
    (ChildrenCoverage93.cons _ _ compact93_node_1228
    (ChildrenCoverage93.cons _ _ compact93_node_1229
    (ChildrenCoverage93.cons _ _ compact93_node_1230
    (ChildrenCoverage93.cons _ _ compact93_node_1249
    (ChildrenCoverage93.cons _ _ compact93_node_1250
    (ChildrenCoverage93.cons _ _ compact93_node_1251
    (ChildrenCoverage93.cons _ _ compact93_node_1252
    (ChildrenCoverage93.cons _ _ compact93_node_1253
    (ChildrenCoverage93.cons _ _ compact93_node_1254
    (ChildrenCoverage93.cons _ _ compact93_node_1255
    (ChildrenCoverage93.cons _ _ compact93_node_1256
    (ChildrenCoverage93.cons _ _ compact93_node_1257
    (ChildrenCoverage93.cons _ _ compact93_node_1258
    (ChildrenCoverage93.cons _ _ compact93_node_1259
    ChildrenCoverage93.nil)))))))))))))))))))))))))

theorem compact93_node_1261 : NodeCoverage93 [28,27] 27 38 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1262 : NodeCoverage93 [28,26] 26 39 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1263 : NodeCoverage93 [28,25] 25 40 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1264 : NodeCoverage93 [28,24] 24 41 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1265 : NodeCoverage93 [28,23] 23 42 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1266 : NodeCoverage93 [28,22] 22 43 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1267 : NodeCoverage93 [28,21] 21 44 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1268 : NodeCoverage93 [28,20] 20 45 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1269 : NodeCoverage93 [28,19] 19 46 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1270 : NodeCoverage93 [28,18] 18 47 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1271 : NodeCoverage93 [28,17] 17 48 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1272 : NodeCoverage93 [28,16] 16 49 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1273 : NodeCoverage93 [28,15] 15 50 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1274 : NodeCoverage93 [28,14,14] 14 37 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1275 : NodeCoverage93 [28,14,13] 13 38 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1276 : NodeCoverage93 [28,14,12] 12 39 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1277 : NodeCoverage93 [28,14,11] 11 40 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1278 : NodeCoverage93 [28,14,10] 10 41 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1279 : NodeCoverage93 [28,14,9] 9 42 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1280 : NodeCoverage93 [28,14,8] 8 43 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1281 : NodeCoverage93 [28,14,7,7,7,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1282 : NodeCoverage93 [28,14,7,7,7,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1283 : NodeCoverage93 [28,14,7,7,7,7,7,7,3] 3 6 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1284 : NodeCoverage93 [28,14,7,7,7,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1281
    (ChildrenCoverage93.cons _ _ compact93_node_1282
    (ChildrenCoverage93.cons _ _ compact93_node_1283
    ChildrenCoverage93.nil)))

theorem compact93_node_1285 : NodeCoverage93 [28,14,7,7,7,7,7,6] 6 10 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1286 : NodeCoverage93 [28,14,7,7,7,7,7,5] 5 11 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1287 : NodeCoverage93 [28,14,7,7,7,7,7,3] 3 13 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1288 : NodeCoverage93 [28,14,7,7,7,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1284
    (ChildrenCoverage93.cons _ _ compact93_node_1285
    (ChildrenCoverage93.cons _ _ compact93_node_1286
    (ChildrenCoverage93.cons _ _ compact93_node_1287
    ChildrenCoverage93.nil))))

theorem compact93_node_1289 : NodeCoverage93 [28,14,7,7,7,7,6] 6 17 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1290 : NodeCoverage93 [28,14,7,7,7,7,5] 5 18 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1291 : NodeCoverage93 [28,14,7,7,7,7,3] 3 20 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1292 : NodeCoverage93 [28,14,7,7,7,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1288
    (ChildrenCoverage93.cons _ _ compact93_node_1289
    (ChildrenCoverage93.cons _ _ compact93_node_1290
    (ChildrenCoverage93.cons _ _ compact93_node_1291
    ChildrenCoverage93.nil))))

theorem compact93_node_1293 : NodeCoverage93 [28,14,7,7,7,6] 6 24 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1294 : NodeCoverage93 [28,14,7,7,7,5] 5 25 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1295 : NodeCoverage93 [28,14,7,7,7,3] 3 27 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1296 : NodeCoverage93 [28,14,7,7,7] 7 30 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1292
    (ChildrenCoverage93.cons _ _ compact93_node_1293
    (ChildrenCoverage93.cons _ _ compact93_node_1294
    (ChildrenCoverage93.cons _ _ compact93_node_1295
    ChildrenCoverage93.nil))))

theorem compact93_node_1297 : NodeCoverage93 [28,14,7,7,6] 6 31 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1298 : NodeCoverage93 [28,14,7,7,5] 5 32 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1299 : NodeCoverage93 [28,14,7,7,3] 3 34 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1300 : NodeCoverage93 [28,14,7,7] 7 37 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1296
    (ChildrenCoverage93.cons _ _ compact93_node_1297
    (ChildrenCoverage93.cons _ _ compact93_node_1298
    (ChildrenCoverage93.cons _ _ compact93_node_1299
    ChildrenCoverage93.nil))))

theorem compact93_node_1301 : NodeCoverage93 [28,14,7,6] 6 38 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1302 : NodeCoverage93 [28,14,7,5] 5 39 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1303 : NodeCoverage93 [28,14,7,3] 3 41 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1304 : NodeCoverage93 [28,14,7] 7 44 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1300
    (ChildrenCoverage93.cons _ _ compact93_node_1301
    (ChildrenCoverage93.cons _ _ compact93_node_1302
    (ChildrenCoverage93.cons _ _ compact93_node_1303
    ChildrenCoverage93.nil))))

theorem compact93_node_1305 : NodeCoverage93 [28,14,6] 6 45 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1306 : NodeCoverage93 [28,14,5] 5 46 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1307 : NodeCoverage93 [28,14,3] 3 48 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1308 : NodeCoverage93 [28,14] 14 51 :=
  node_fork93 (B := [14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1274
    (ChildrenCoverage93.cons _ _ compact93_node_1275
    (ChildrenCoverage93.cons _ _ compact93_node_1276
    (ChildrenCoverage93.cons _ _ compact93_node_1277
    (ChildrenCoverage93.cons _ _ compact93_node_1278
    (ChildrenCoverage93.cons _ _ compact93_node_1279
    (ChildrenCoverage93.cons _ _ compact93_node_1280
    (ChildrenCoverage93.cons _ _ compact93_node_1304
    (ChildrenCoverage93.cons _ _ compact93_node_1305
    (ChildrenCoverage93.cons _ _ compact93_node_1306
    (ChildrenCoverage93.cons _ _ compact93_node_1307
    ChildrenCoverage93.nil)))))))))))

theorem compact93_node_1309 : NodeCoverage93 [28,13] 13 52 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
