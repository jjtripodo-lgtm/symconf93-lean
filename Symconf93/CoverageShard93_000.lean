module
public import Symconf93.AllDemandBanks93

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0000 : NodeCoverage93 [93] 93 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_0001 : NodeCoverage93 [90] 90 3 :=
  demand_node_prune93 90 compact93_demands_90 compact93_demands_90_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0002 : NodeCoverage93 [89] 89 4 :=
  demand_node_prune93 89 compact93_demands_89 compact93_demands_89_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0003 : NodeCoverage93 [88] 88 5 :=
  demand_node_prune93 88 compact93_demands_88 compact93_demands_88_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0004 : NodeCoverage93 [87] 87 6 :=
  demand_node_prune93 87 compact93_demands_87 compact93_demands_87_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0005 : NodeCoverage93 [86] 86 7 :=
  demand_node_prune93 86 compact93_demands_86 compact93_demands_86_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0006 : NodeCoverage93 [85] 85 8 :=
  demand_node_prune93 85 compact93_demands_85 compact93_demands_85_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0007 : NodeCoverage93 [84] 84 9 :=
  demand_node_prune93 84 compact93_demands_84 compact93_demands_84_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0008 : NodeCoverage93 [83] 83 10 :=
  demand_node_prune93 83 compact93_demands_83 compact93_demands_83_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0009 : NodeCoverage93 [82] 82 11 :=
  demand_node_prune93 82 compact93_demands_82 compact93_demands_82_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0010 : NodeCoverage93 [81] 81 12 :=
  demand_node_prune93 81 compact93_demands_81 compact93_demands_81_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0011 : NodeCoverage93 [80] 80 13 :=
  demand_node_prune93 80 compact93_demands_80 compact93_demands_80_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0012 : NodeCoverage93 [79] 79 14 :=
  demand_node_prune93 79 compact93_demands_79 compact93_demands_79_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0013 : NodeCoverage93 [78] 78 15 :=
  demand_node_prune93 78 compact93_demands_78 compact93_demands_78_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0014 : NodeCoverage93 [77] 77 16 :=
  demand_node_prune93 77 compact93_demands_77 compact93_demands_77_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0015 : NodeCoverage93 [76] 76 17 :=
  demand_node_prune93 76 compact93_demands_76 compact93_demands_76_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0016 : NodeCoverage93 [75] 75 18 :=
  demand_node_prune93 75 compact93_demands_75 compact93_demands_75_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0017 : NodeCoverage93 [74] 74 19 :=
  demand_node_prune93 74 compact93_demands_74 compact93_demands_74_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0018 : NodeCoverage93 [73] 73 20 :=
  demand_node_prune93 73 compact93_demands_73 compact93_demands_73_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0019 : NodeCoverage93 [72,21] 21 0 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0020 : NodeCoverage93 [72,18] 18 3 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0021 : NodeCoverage93 [72,17] 17 4 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0022 : NodeCoverage93 [72,16] 16 5 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0023 : NodeCoverage93 [72,15] 15 6 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0024 : NodeCoverage93 [72,14] 14 7 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0025 : NodeCoverage93 [72,13] 13 8 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0026 : NodeCoverage93 [72,12,9] 9 0 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0027 : NodeCoverage93 [72,12,6] 6 3 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0028 : NodeCoverage93 [72,12,5] 5 4 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0029 : NodeCoverage93 [72,12,3] 3 6 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0030 : NodeCoverage93 [72,12] 12 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0026
    (ChildrenCoverage93.cons _ _ compact93_node_0027
    (ChildrenCoverage93.cons _ _ compact93_node_0028
    (ChildrenCoverage93.cons _ _ compact93_node_0029
    ChildrenCoverage93.nil))))

theorem compact93_node_0031 : NodeCoverage93 [72,11] 11 10 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0032 : NodeCoverage93 [72,10] 10 11 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0033 : NodeCoverage93 [72,9] 9 12 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0034 : NodeCoverage93 [72,8] 8 13 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0035 : NodeCoverage93 [72,7] 7 14 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0036 : NodeCoverage93 [72,6] 6 15 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0037 : NodeCoverage93 [72,5] 5 16 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0038 : NodeCoverage93 [72,3] 3 18 :=
  demand_node_prune93 72 compact93_demands_72 compact93_demands_72_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0039 : NodeCoverage93 [72] 72 21 :=
  node_fork93 (B := [21,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0019
    (ChildrenCoverage93.cons _ _ compact93_node_0020
    (ChildrenCoverage93.cons _ _ compact93_node_0021
    (ChildrenCoverage93.cons _ _ compact93_node_0022
    (ChildrenCoverage93.cons _ _ compact93_node_0023
    (ChildrenCoverage93.cons _ _ compact93_node_0024
    (ChildrenCoverage93.cons _ _ compact93_node_0025
    (ChildrenCoverage93.cons _ _ compact93_node_0030
    (ChildrenCoverage93.cons _ _ compact93_node_0031
    (ChildrenCoverage93.cons _ _ compact93_node_0032
    (ChildrenCoverage93.cons _ _ compact93_node_0033
    (ChildrenCoverage93.cons _ _ compact93_node_0034
    (ChildrenCoverage93.cons _ _ compact93_node_0035
    (ChildrenCoverage93.cons _ _ compact93_node_0036
    (ChildrenCoverage93.cons _ _ compact93_node_0037
    (ChildrenCoverage93.cons _ _ compact93_node_0038
    ChildrenCoverage93.nil))))))))))))))))

theorem compact93_node_0040 : NodeCoverage93 [71] 71 22 :=
  demand_node_prune93 71 compact93_demands_71 compact93_demands_71_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0041 : NodeCoverage93 [70] 70 23 :=
  demand_node_prune93 70 compact93_demands_70 compact93_demands_70_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0042 : NodeCoverage93 [69] 69 24 :=
  demand_node_prune93 69 compact93_demands_69 compact93_demands_69_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0043 : NodeCoverage93 [68] 68 25 :=
  demand_node_prune93 68 compact93_demands_68 compact93_demands_68_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0044 : NodeCoverage93 [67] 67 26 :=
  demand_node_prune93 67 compact93_demands_67 compact93_demands_67_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0045 : NodeCoverage93 [66] 66 27 :=
  demand_node_prune93 66 compact93_demands_66 compact93_demands_66_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0046 : NodeCoverage93 [65] 65 28 :=
  demand_node_prune93 65 compact93_demands_65 compact93_demands_65_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0047 : NodeCoverage93 [64] 64 29 :=
  demand_node_prune93 64 compact93_demands_64 compact93_demands_64_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0048 : NodeCoverage93 [63,30] 30 0 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0049 : NodeCoverage93 [63,27] 27 3 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0050 : NodeCoverage93 [63,26] 26 4 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0051 : NodeCoverage93 [63,25] 25 5 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0052 : NodeCoverage93 [63,24] 24 6 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0053 : NodeCoverage93 [63,23] 23 7 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0054 : NodeCoverage93 [63,22] 22 8 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0055 : NodeCoverage93 [63,21] 21 9 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0056 : NodeCoverage93 [63,20] 20 10 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0057 : NodeCoverage93 [63,19] 19 11 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0058 : NodeCoverage93 [63,18] 18 12 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0059 : NodeCoverage93 [63,17] 17 13 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0060 : NodeCoverage93 [63,16] 16 14 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0061 : NodeCoverage93 [63,15] 15 15 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0062 : NodeCoverage93 [63,14] 14 16 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0063 : NodeCoverage93 [63,13] 13 17 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0064 : NodeCoverage93 [63,12] 12 18 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0065 : NodeCoverage93 [63,11] 11 19 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0066 : NodeCoverage93 [63,10] 10 20 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0067 : NodeCoverage93 [63,9,9,9,3] 3 0 :=
  node_no_weak_demand93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0068 : NodeCoverage93 [63,9,9,9] 9 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0067
    ChildrenCoverage93.nil)

theorem compact93_node_0069 : NodeCoverage93 [63,9,9,8] 8 4 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0070 : NodeCoverage93 [63,9,9,7] 7 5 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0071 : NodeCoverage93 [63,9,9,6] 6 6 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0072 : NodeCoverage93 [63,9,9,5] 5 7 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0073 : NodeCoverage93 [63,9,9,3] 3 9 :=
  demand_node_prune93 63 compact93_demands_63 compact93_demands_63_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0074 : NodeCoverage93 [63,9,9] 9 12 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0068
    (ChildrenCoverage93.cons _ _ compact93_node_0069
    (ChildrenCoverage93.cons _ _ compact93_node_0070
    (ChildrenCoverage93.cons _ _ compact93_node_0071
    (ChildrenCoverage93.cons _ _ compact93_node_0072
    (ChildrenCoverage93.cons _ _ compact93_node_0073
    ChildrenCoverage93.nil))))))

end Symconf93
