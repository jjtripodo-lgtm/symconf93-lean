module
public import Symconf93.CoverageParallelLow93_037

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_4138 : NodeCoverage93 [5,5,5,3] 3 75 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4139 : NodeCoverage93 [5,5,5] 5 78 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4137
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4138
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4140 : NodeCoverage93 [5,5,3] 3 80 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4141 : NodeCoverage93 [5,5] 5 83 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4139
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4140
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4142 : NodeCoverage93 [5,3] 3 85 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_4143 : NodeCoverage93 [5] 5 88 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4141
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4142
    ChildrenCoverage93.nil))

theorem compact_parallel93_node_4144 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact_parallel93_node_4145 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4144
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4146 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4145
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4147 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 9 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4146
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4148 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 12 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4147
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4149 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 15 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4148
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4150 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 18 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4149
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4151 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 21 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4150
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4152 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 24 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4151
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4153 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 27 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4152
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4154 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 30 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4153
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4155 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 33 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4154
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4156 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 36 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4155
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4157 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 39 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4156
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4158 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 42 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4157
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4159 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 45 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4158
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4160 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 48 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4159
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4161 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3,3] 3 51 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4160
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4162 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3,3] 3 54 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4161
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4163 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3,3] 3 57 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4162
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4164 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3,3] 3 60 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4163
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4165 : NodeCoverage93 [3,3,3,3,3,3,3,3,3,3] 3 63 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4164
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4166 : NodeCoverage93 [3,3,3,3,3,3,3,3,3] 3 66 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4165
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4167 : NodeCoverage93 [3,3,3,3,3,3,3,3] 3 69 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4166
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4168 : NodeCoverage93 [3,3,3,3,3,3,3] 3 72 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4167
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4169 : NodeCoverage93 [3,3,3,3,3,3] 3 75 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4168
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4170 : NodeCoverage93 [3,3,3,3,3] 3 78 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4169
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4171 : NodeCoverage93 [3,3,3,3] 3 81 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4170
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4172 : NodeCoverage93 [3,3,3] 3 84 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4171
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4173 : NodeCoverage93 [3,3] 3 87 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4172
    ChildrenCoverage93.nil)

theorem compact_parallel93_node_4174 : NodeCoverage93 [3] 3 90 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_4173
    ChildrenCoverage93.nil)

end Symconf93
