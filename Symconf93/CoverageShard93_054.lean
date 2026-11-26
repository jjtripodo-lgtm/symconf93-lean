module
public import Symconf93.CoverageShard93_053

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1950 : NodeCoverage93 [21,15,11] 11 46 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1951 : NodeCoverage93 [21,15,10] 10 47 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1952 : NodeCoverage93 [21,15,9] 9 48 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1953 : NodeCoverage93 [21,15,8] 8 49 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1954 : NodeCoverage93 [21,15,7] 7 50 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1955 : NodeCoverage93 [21,15,6] 6 51 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1956 : NodeCoverage93 [21,15,5] 5 52 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1957 : NodeCoverage93 [21,15,3] 3 54 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1958 : NodeCoverage93 [21,15] 15 57 :=
  node_fork93 (B := [15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1946
    (ChildrenCoverage93.cons _ _ compact93_node_1947
    (ChildrenCoverage93.cons _ _ compact93_node_1948
    (ChildrenCoverage93.cons _ _ compact93_node_1949
    (ChildrenCoverage93.cons _ _ compact93_node_1950
    (ChildrenCoverage93.cons _ _ compact93_node_1951
    (ChildrenCoverage93.cons _ _ compact93_node_1952
    (ChildrenCoverage93.cons _ _ compact93_node_1953
    (ChildrenCoverage93.cons _ _ compact93_node_1954
    (ChildrenCoverage93.cons _ _ compact93_node_1955
    (ChildrenCoverage93.cons _ _ compact93_node_1956
    (ChildrenCoverage93.cons _ _ compact93_node_1957
    ChildrenCoverage93.nil))))))))))))

theorem compact93_node_1959 : NodeCoverage93 [21,14] 14 58 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1960 : NodeCoverage93 [21,13,13] 13 46 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1961 : NodeCoverage93 [21,13,12] 12 47 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1962 : NodeCoverage93 [21,13,11] 11 48 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1963 : NodeCoverage93 [21,13,10] 10 49 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1964 : NodeCoverage93 [21,13,9] 9 50 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1965 : NodeCoverage93 [21,13,8] 8 51 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1966 : NodeCoverage93 [21,13,7] 7 52 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1967 : NodeCoverage93 [21,13,6] 6 53 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1968 : NodeCoverage93 [21,13,5] 5 54 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1969 : NodeCoverage93 [21,13,3] 3 56 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1970 : NodeCoverage93 [21,13] 13 59 :=
  node_fork93 (B := [13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1960
    (ChildrenCoverage93.cons _ _ compact93_node_1961
    (ChildrenCoverage93.cons _ _ compact93_node_1962
    (ChildrenCoverage93.cons _ _ compact93_node_1963
    (ChildrenCoverage93.cons _ _ compact93_node_1964
    (ChildrenCoverage93.cons _ _ compact93_node_1965
    (ChildrenCoverage93.cons _ _ compact93_node_1966
    (ChildrenCoverage93.cons _ _ compact93_node_1967
    (ChildrenCoverage93.cons _ _ compact93_node_1968
    (ChildrenCoverage93.cons _ _ compact93_node_1969
    ChildrenCoverage93.nil))))))))))

theorem compact93_node_1971 : NodeCoverage93 [21,12,12] 12 48 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1972 : NodeCoverage93 [21,12,11] 11 49 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1973 : NodeCoverage93 [21,12,10] 10 50 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1974 : NodeCoverage93 [21,12,9] 9 51 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1975 : NodeCoverage93 [21,12,8] 8 52 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1976 : NodeCoverage93 [21,12,7] 7 53 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1977 : NodeCoverage93 [21,12,6] 6 54 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1978 : NodeCoverage93 [21,12,5] 5 55 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1979 : NodeCoverage93 [21,12,3] 3 57 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1980 : NodeCoverage93 [21,12] 12 60 :=
  node_fork93 (B := [12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1971
    (ChildrenCoverage93.cons _ _ compact93_node_1972
    (ChildrenCoverage93.cons _ _ compact93_node_1973
    (ChildrenCoverage93.cons _ _ compact93_node_1974
    (ChildrenCoverage93.cons _ _ compact93_node_1975
    (ChildrenCoverage93.cons _ _ compact93_node_1976
    (ChildrenCoverage93.cons _ _ compact93_node_1977
    (ChildrenCoverage93.cons _ _ compact93_node_1978
    (ChildrenCoverage93.cons _ _ compact93_node_1979
    ChildrenCoverage93.nil)))))))))

theorem compact93_node_1981 : NodeCoverage93 [21,11,11] 11 50 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1982 : NodeCoverage93 [21,11,10] 10 51 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
