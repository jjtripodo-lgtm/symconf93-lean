module
public import Symconf93.CoverageShard93_035

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1160 : NodeCoverage93 [30,3] 3 60 :=
  demand_node_prune93 30 compact93_demands_30 compact93_demands_30_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1161 : NodeCoverage93 [30] 30 63 :=
  node_fork93 (B := [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1053
    (ChildrenCoverage93.cons _ _ compact93_node_1054
    (ChildrenCoverage93.cons _ _ compact93_node_1055
    (ChildrenCoverage93.cons _ _ compact93_node_1056
    (ChildrenCoverage93.cons _ _ compact93_node_1057
    (ChildrenCoverage93.cons _ _ compact93_node_1058
    (ChildrenCoverage93.cons _ _ compact93_node_1059
    (ChildrenCoverage93.cons _ _ compact93_node_1060
    (ChildrenCoverage93.cons _ _ compact93_node_1061
    (ChildrenCoverage93.cons _ _ compact93_node_1062
    (ChildrenCoverage93.cons _ _ compact93_node_1063
    (ChildrenCoverage93.cons _ _ compact93_node_1064
    (ChildrenCoverage93.cons _ _ compact93_node_1065
    (ChildrenCoverage93.cons _ _ compact93_node_1066
    (ChildrenCoverage93.cons _ _ compact93_node_1067
    (ChildrenCoverage93.cons _ _ compact93_node_1104
    (ChildrenCoverage93.cons _ _ compact93_node_1105
    (ChildrenCoverage93.cons _ _ compact93_node_1106
    (ChildrenCoverage93.cons _ _ compact93_node_1107
    (ChildrenCoverage93.cons _ _ compact93_node_1108
    (ChildrenCoverage93.cons _ _ compact93_node_1154
    (ChildrenCoverage93.cons _ _ compact93_node_1155
    (ChildrenCoverage93.cons _ _ compact93_node_1156
    (ChildrenCoverage93.cons _ _ compact93_node_1157
    (ChildrenCoverage93.cons _ _ compact93_node_1158
    (ChildrenCoverage93.cons _ _ compact93_node_1159
    (ChildrenCoverage93.cons _ _ compact93_node_1160
    ChildrenCoverage93.nil)))))))))))))))))))))))))))

theorem compact93_node_1162 : NodeCoverage93 [29,29,29,6] 6 0 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1163 : NodeCoverage93 [29,29,29,3] 3 3 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1164 : NodeCoverage93 [29,29,29] 29 6 :=
  node_fork93 (B := [6,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1162
    (ChildrenCoverage93.cons _ _ compact93_node_1163
    ChildrenCoverage93.nil))

theorem compact93_node_1165 : NodeCoverage93 [29,29,28] 28 7 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1166 : NodeCoverage93 [29,29,27] 27 8 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1167 : NodeCoverage93 [29,29,26] 26 9 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1168 : NodeCoverage93 [29,29,25] 25 10 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1169 : NodeCoverage93 [29,29,24] 24 11 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1170 : NodeCoverage93 [29,29,23] 23 12 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1171 : NodeCoverage93 [29,29,22] 22 13 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1172 : NodeCoverage93 [29,29,21] 21 14 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1173 : NodeCoverage93 [29,29,20] 20 15 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1174 : NodeCoverage93 [29,29,19] 19 16 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1175 : NodeCoverage93 [29,29,18] 18 17 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1176 : NodeCoverage93 [29,29,17] 17 18 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1177 : NodeCoverage93 [29,29,16] 16 19 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1178 : NodeCoverage93 [29,29,15] 15 20 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1179 : NodeCoverage93 [29,29,14] 14 21 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1180 : NodeCoverage93 [29,29,13] 13 22 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1181 : NodeCoverage93 [29,29,12] 12 23 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1182 : NodeCoverage93 [29,29,11] 11 24 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1183 : NodeCoverage93 [29,29,10] 10 25 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1184 : NodeCoverage93 [29,29,9] 9 26 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1185 : NodeCoverage93 [29,29,8] 8 27 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1186 : NodeCoverage93 [29,29,7] 7 28 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1187 : NodeCoverage93 [29,29,6] 6 29 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1188 : NodeCoverage93 [29,29,5] 5 30 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1189 : NodeCoverage93 [29,29,3] 3 32 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1190 : NodeCoverage93 [29,29] 29 35 :=
  node_fork93 (B := [29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1164
    (ChildrenCoverage93.cons _ _ compact93_node_1165
    (ChildrenCoverage93.cons _ _ compact93_node_1166
    (ChildrenCoverage93.cons _ _ compact93_node_1167
    (ChildrenCoverage93.cons _ _ compact93_node_1168
    (ChildrenCoverage93.cons _ _ compact93_node_1169
    (ChildrenCoverage93.cons _ _ compact93_node_1170
    (ChildrenCoverage93.cons _ _ compact93_node_1171
    (ChildrenCoverage93.cons _ _ compact93_node_1172
    (ChildrenCoverage93.cons _ _ compact93_node_1173
    (ChildrenCoverage93.cons _ _ compact93_node_1174
    (ChildrenCoverage93.cons _ _ compact93_node_1175
    (ChildrenCoverage93.cons _ _ compact93_node_1176
    (ChildrenCoverage93.cons _ _ compact93_node_1177
    (ChildrenCoverage93.cons _ _ compact93_node_1178
    (ChildrenCoverage93.cons _ _ compact93_node_1179
    (ChildrenCoverage93.cons _ _ compact93_node_1180
    (ChildrenCoverage93.cons _ _ compact93_node_1181
    (ChildrenCoverage93.cons _ _ compact93_node_1182
    (ChildrenCoverage93.cons _ _ compact93_node_1183
    (ChildrenCoverage93.cons _ _ compact93_node_1184
    (ChildrenCoverage93.cons _ _ compact93_node_1185
    (ChildrenCoverage93.cons _ _ compact93_node_1186
    (ChildrenCoverage93.cons _ _ compact93_node_1187
    (ChildrenCoverage93.cons _ _ compact93_node_1188
    (ChildrenCoverage93.cons _ _ compact93_node_1189
    ChildrenCoverage93.nil))))))))))))))))))))))))))

theorem compact93_node_1191 : NodeCoverage93 [29,28] 28 36 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1192 : NodeCoverage93 [29,27] 27 37 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1193 : NodeCoverage93 [29,26] 26 38 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1194 : NodeCoverage93 [29,25] 25 39 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1195 : NodeCoverage93 [29,24] 24 40 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1196 : NodeCoverage93 [29,23] 23 41 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1197 : NodeCoverage93 [29,22] 22 42 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1198 : NodeCoverage93 [29,21] 21 43 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1199 : NodeCoverage93 [29,20] 20 44 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1200 : NodeCoverage93 [29,19] 19 45 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1201 : NodeCoverage93 [29,18] 18 46 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1202 : NodeCoverage93 [29,17] 17 47 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1203 : NodeCoverage93 [29,16] 16 48 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1204 : NodeCoverage93 [29,15] 15 49 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1205 : NodeCoverage93 [29,14] 14 50 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1206 : NodeCoverage93 [29,13] 13 51 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1207 : NodeCoverage93 [29,12] 12 52 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1208 : NodeCoverage93 [29,11] 11 53 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1209 : NodeCoverage93 [29,10] 10 54 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1210 : NodeCoverage93 [29,9] 9 55 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1211 : NodeCoverage93 [29,8] 8 56 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1212 : NodeCoverage93 [29,7] 7 57 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1213 : NodeCoverage93 [29,6] 6 58 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1214 : NodeCoverage93 [29,5] 5 59 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1215 : NodeCoverage93 [29,3] 3 61 :=
  demand_node_prune93 29 compact93_demands_29 compact93_demands_29_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1216 : NodeCoverage93 [29] 29 64 :=
  node_fork93 (B := [29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1190
    (ChildrenCoverage93.cons _ _ compact93_node_1191
    (ChildrenCoverage93.cons _ _ compact93_node_1192
    (ChildrenCoverage93.cons _ _ compact93_node_1193
    (ChildrenCoverage93.cons _ _ compact93_node_1194
    (ChildrenCoverage93.cons _ _ compact93_node_1195
    (ChildrenCoverage93.cons _ _ compact93_node_1196
    (ChildrenCoverage93.cons _ _ compact93_node_1197
    (ChildrenCoverage93.cons _ _ compact93_node_1198
    (ChildrenCoverage93.cons _ _ compact93_node_1199
    (ChildrenCoverage93.cons _ _ compact93_node_1200
    (ChildrenCoverage93.cons _ _ compact93_node_1201
    (ChildrenCoverage93.cons _ _ compact93_node_1202
    (ChildrenCoverage93.cons _ _ compact93_node_1203
    (ChildrenCoverage93.cons _ _ compact93_node_1204
    (ChildrenCoverage93.cons _ _ compact93_node_1205
    (ChildrenCoverage93.cons _ _ compact93_node_1206
    (ChildrenCoverage93.cons _ _ compact93_node_1207
    (ChildrenCoverage93.cons _ _ compact93_node_1208
    (ChildrenCoverage93.cons _ _ compact93_node_1209
    (ChildrenCoverage93.cons _ _ compact93_node_1210
    (ChildrenCoverage93.cons _ _ compact93_node_1211
    (ChildrenCoverage93.cons _ _ compact93_node_1212
    (ChildrenCoverage93.cons _ _ compact93_node_1213
    (ChildrenCoverage93.cons _ _ compact93_node_1214
    (ChildrenCoverage93.cons _ _ compact93_node_1215
    ChildrenCoverage93.nil))))))))))))))))))))))))))

theorem compact93_node_1217 : NodeCoverage93 [28,28,28] 28 9 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1218 : NodeCoverage93 [28,28,27] 27 10 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1219 : NodeCoverage93 [28,28,26] 26 11 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1220 : NodeCoverage93 [28,28,25] 25 12 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1221 : NodeCoverage93 [28,28,24] 24 13 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1222 : NodeCoverage93 [28,28,23] 23 14 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1223 : NodeCoverage93 [28,28,22] 22 15 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1224 : NodeCoverage93 [28,28,21] 21 16 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1225 : NodeCoverage93 [28,28,20] 20 17 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1226 : NodeCoverage93 [28,28,19] 19 18 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1227 : NodeCoverage93 [28,28,18] 18 19 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1228 : NodeCoverage93 [28,28,17] 17 20 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1229 : NodeCoverage93 [28,28,16] 16 21 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1230 : NodeCoverage93 [28,28,15] 15 22 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1231 : NodeCoverage93 [28,28,14,14] 14 9 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1232 : NodeCoverage93 [28,28,14,13] 13 10 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1233 : NodeCoverage93 [28,28,14,12] 12 11 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1234 : NodeCoverage93 [28,28,14,11] 11 12 :=
  demand_node_prune93 28 compact93_demands_28 compact93_demands_28_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
