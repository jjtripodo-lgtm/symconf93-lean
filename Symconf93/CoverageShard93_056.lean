module
public import Symconf93.CoverageShard93_055

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_2029 : NodeCoverage93 [21,7,7,7,7,7,3] 3 34 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2030 : NodeCoverage93 [21,7,7,7,7,7] 7 37 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2026
    (ChildrenCoverage93.cons _ _ compact93_node_2027
    (ChildrenCoverage93.cons _ _ compact93_node_2028
    (ChildrenCoverage93.cons _ _ compact93_node_2029
    ChildrenCoverage93.nil))))

theorem compact93_node_2031 : NodeCoverage93 [21,7,7,7,7,6] 6 38 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2032 : NodeCoverage93 [21,7,7,7,7,5] 5 39 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2033 : NodeCoverage93 [21,7,7,7,7,3] 3 41 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2034 : NodeCoverage93 [21,7,7,7,7] 7 44 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2030
    (ChildrenCoverage93.cons _ _ compact93_node_2031
    (ChildrenCoverage93.cons _ _ compact93_node_2032
    (ChildrenCoverage93.cons _ _ compact93_node_2033
    ChildrenCoverage93.nil))))

theorem compact93_node_2035 : NodeCoverage93 [21,7,7,7,6] 6 45 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2036 : NodeCoverage93 [21,7,7,7,5] 5 46 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2037 : NodeCoverage93 [21,7,7,7,3] 3 48 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2038 : NodeCoverage93 [21,7,7,7] 7 51 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2034
    (ChildrenCoverage93.cons _ _ compact93_node_2035
    (ChildrenCoverage93.cons _ _ compact93_node_2036
    (ChildrenCoverage93.cons _ _ compact93_node_2037
    ChildrenCoverage93.nil))))

theorem compact93_node_2039 : NodeCoverage93 [21,7,7,6] 6 52 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2040 : NodeCoverage93 [21,7,7,5] 5 53 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2041 : NodeCoverage93 [21,7,7,3] 3 55 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2042 : NodeCoverage93 [21,7,7] 7 58 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2038
    (ChildrenCoverage93.cons _ _ compact93_node_2039
    (ChildrenCoverage93.cons _ _ compact93_node_2040
    (ChildrenCoverage93.cons _ _ compact93_node_2041
    ChildrenCoverage93.nil))))

theorem compact93_node_2043 : NodeCoverage93 [21,7,6] 6 59 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2044 : NodeCoverage93 [21,7,5] 5 60 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2045 : NodeCoverage93 [21,7,3] 3 62 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2046 : NodeCoverage93 [21,7] 7 65 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2042
    (ChildrenCoverage93.cons _ _ compact93_node_2043
    (ChildrenCoverage93.cons _ _ compact93_node_2044
    (ChildrenCoverage93.cons _ _ compact93_node_2045
    ChildrenCoverage93.nil))))

theorem compact93_node_2047 : NodeCoverage93 [21,6] 6 66 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2048 : NodeCoverage93 [21,5] 5 67 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2049 : NodeCoverage93 [21,3] 3 69 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2050 : NodeCoverage93 [21] 21 72 :=
  node_fork93 (B := [21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1927
    (ChildrenCoverage93.cons _ _ compact93_node_1928
    (ChildrenCoverage93.cons _ _ compact93_node_1929
    (ChildrenCoverage93.cons _ _ compact93_node_1930
    (ChildrenCoverage93.cons _ _ compact93_node_1931
    (ChildrenCoverage93.cons _ _ compact93_node_1945
    (ChildrenCoverage93.cons _ _ compact93_node_1958
    (ChildrenCoverage93.cons _ _ compact93_node_1959
    (ChildrenCoverage93.cons _ _ compact93_node_1970
    (ChildrenCoverage93.cons _ _ compact93_node_1980
    (ChildrenCoverage93.cons _ _ compact93_node_1989
    (ChildrenCoverage93.cons _ _ compact93_node_1997
    (ChildrenCoverage93.cons _ _ compact93_node_2004
    (ChildrenCoverage93.cons _ _ compact93_node_2005
    (ChildrenCoverage93.cons _ _ compact93_node_2046
    (ChildrenCoverage93.cons _ _ compact93_node_2047
    (ChildrenCoverage93.cons _ _ compact93_node_2048
    (ChildrenCoverage93.cons _ _ compact93_node_2049
    ChildrenCoverage93.nil))))))))))))))))))

theorem compact93_node_2051 : NodeCoverage93 [20,20,20,20,13] 13 0 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2052 : NodeCoverage93 [20,20,20,20,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2053 : NodeCoverage93 [20,20,20,20,9] 9 4 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2054 : NodeCoverage93 [20,20,20,20,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2055 : NodeCoverage93 [20,20,20,20,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2056 : NodeCoverage93 [20,20,20,20,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2057 : NodeCoverage93 [20,20,20,20,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2058 : NodeCoverage93 [20,20,20,20,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2057
    ChildrenCoverage93.nil)

theorem compact93_node_2059 : NodeCoverage93 [20,20,20,20,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2060 : NodeCoverage93 [20,20,20,20,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2058
    (ChildrenCoverage93.cons _ _ compact93_node_2059
    ChildrenCoverage93.nil))

theorem compact93_node_2061 : NodeCoverage93 [20,20,20,20,3] 3 10 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2062 : NodeCoverage93 [20,20,20,20] 20 13 :=
  node_fork93 (B := [13,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2051
    (ChildrenCoverage93.cons _ _ compact93_node_2052
    (ChildrenCoverage93.cons _ _ compact93_node_2053
    (ChildrenCoverage93.cons _ _ compact93_node_2054
    (ChildrenCoverage93.cons _ _ compact93_node_2055
    (ChildrenCoverage93.cons _ _ compact93_node_2056
    (ChildrenCoverage93.cons _ _ compact93_node_2060
    (ChildrenCoverage93.cons _ _ compact93_node_2061
    ChildrenCoverage93.nil))))))))

theorem compact93_node_2063 : NodeCoverage93 [20,20,20,19] 19 14 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2064 : NodeCoverage93 [20,20,20,18] 18 15 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2065 : NodeCoverage93 [20,20,20,17] 17 16 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2066 : NodeCoverage93 [20,20,20,16] 16 17 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2067 : NodeCoverage93 [20,20,20,15] 15 18 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2068 : NodeCoverage93 [20,20,20,14] 14 19 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2069 : NodeCoverage93 [20,20,20,13] 13 20 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2070 : NodeCoverage93 [20,20,20,12] 12 21 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2071 : NodeCoverage93 [20,20,20,11] 11 22 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2072 : NodeCoverage93 [20,20,20,10,10,10] 10 3 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2073 : NodeCoverage93 [20,20,20,10,10,9] 9 4 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2074 : NodeCoverage93 [20,20,20,10,10,8] 8 5 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2075 : NodeCoverage93 [20,20,20,10,10,7] 7 6 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2076 : NodeCoverage93 [20,20,20,10,10,6] 6 7 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2077 : NodeCoverage93 [20,20,20,10,10,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2078 : NodeCoverage93 [20,20,20,10,10,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2077
    ChildrenCoverage93.nil)

theorem compact93_node_2079 : NodeCoverage93 [20,20,20,10,10,5,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2080 : NodeCoverage93 [20,20,20,10,10,5] 5 8 :=
  node_fork93 (B := [5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2078
    (ChildrenCoverage93.cons _ _ compact93_node_2079
    ChildrenCoverage93.nil))

theorem compact93_node_2081 : NodeCoverage93 [20,20,20,10,10,3] 3 10 :=
  demand_node_prune93 20 compact93_demands_20 compact93_demands_20_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2082 : NodeCoverage93 [20,20,20,10,10] 10 13 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2072
    (ChildrenCoverage93.cons _ _ compact93_node_2073
    (ChildrenCoverage93.cons _ _ compact93_node_2074
    (ChildrenCoverage93.cons _ _ compact93_node_2075
    (ChildrenCoverage93.cons _ _ compact93_node_2076
    (ChildrenCoverage93.cons _ _ compact93_node_2080
    (ChildrenCoverage93.cons _ _ compact93_node_2081
    ChildrenCoverage93.nil)))))))

theorem compact93_node_2083 : NodeCoverage93 [20,20,20,10,9] 9 14 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2084 : NodeCoverage93 [20,20,20,10,8] 8 15 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2085 : NodeCoverage93 [20,20,20,10,7] 7 16 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2086 : NodeCoverage93 [20,20,20,10,6] 6 17 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2087 : NodeCoverage93 [20,20,20,10,5,5,5,5,3] 3 0 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2088 : NodeCoverage93 [20,20,20,10,5,5,5,5] 5 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2087
    ChildrenCoverage93.nil)

end Symconf93
