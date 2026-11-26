module
public import Symconf93.CoverageShard93_052

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1915 : NodeCoverage93 [21,21,7,7,7] 7 30 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1911
    (ChildrenCoverage93.cons _ _ compact93_node_1912
    (ChildrenCoverage93.cons _ _ compact93_node_1913
    (ChildrenCoverage93.cons _ _ compact93_node_1914
    ChildrenCoverage93.nil))))

theorem compact93_node_1916 : NodeCoverage93 [21,21,7,7,6] 6 31 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1917 : NodeCoverage93 [21,21,7,7,5] 5 32 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1918 : NodeCoverage93 [21,21,7,7,3] 3 34 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1919 : NodeCoverage93 [21,21,7,7] 7 37 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1915
    (ChildrenCoverage93.cons _ _ compact93_node_1916
    (ChildrenCoverage93.cons _ _ compact93_node_1917
    (ChildrenCoverage93.cons _ _ compact93_node_1918
    ChildrenCoverage93.nil))))

theorem compact93_node_1920 : NodeCoverage93 [21,21,7,6] 6 38 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1921 : NodeCoverage93 [21,21,7,5] 5 39 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1922 : NodeCoverage93 [21,21,7,3] 3 41 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1923 : NodeCoverage93 [21,21,7] 7 44 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1919
    (ChildrenCoverage93.cons _ _ compact93_node_1920
    (ChildrenCoverage93.cons _ _ compact93_node_1921
    (ChildrenCoverage93.cons _ _ compact93_node_1922
    ChildrenCoverage93.nil))))

theorem compact93_node_1924 : NodeCoverage93 [21,21,6] 6 45 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1925 : NodeCoverage93 [21,21,5] 5 46 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1926 : NodeCoverage93 [21,21,3] 3 48 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1927 : NodeCoverage93 [21,21] 21 51 :=
  node_fork93 (B := [21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1881
    (ChildrenCoverage93.cons _ _ compact93_node_1882
    (ChildrenCoverage93.cons _ _ compact93_node_1883
    (ChildrenCoverage93.cons _ _ compact93_node_1884
    (ChildrenCoverage93.cons _ _ compact93_node_1885
    (ChildrenCoverage93.cons _ _ compact93_node_1886
    (ChildrenCoverage93.cons _ _ compact93_node_1887
    (ChildrenCoverage93.cons _ _ compact93_node_1888
    (ChildrenCoverage93.cons _ _ compact93_node_1889
    (ChildrenCoverage93.cons _ _ compact93_node_1890
    (ChildrenCoverage93.cons _ _ compact93_node_1891
    (ChildrenCoverage93.cons _ _ compact93_node_1892
    (ChildrenCoverage93.cons _ _ compact93_node_1893
    (ChildrenCoverage93.cons _ _ compact93_node_1894
    (ChildrenCoverage93.cons _ _ compact93_node_1923
    (ChildrenCoverage93.cons _ _ compact93_node_1924
    (ChildrenCoverage93.cons _ _ compact93_node_1925
    (ChildrenCoverage93.cons _ _ compact93_node_1926
    ChildrenCoverage93.nil))))))))))))))))))

theorem compact93_node_1928 : NodeCoverage93 [21,20] 20 52 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1929 : NodeCoverage93 [21,19] 19 53 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1930 : NodeCoverage93 [21,18] 18 54 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1931 : NodeCoverage93 [21,17] 17 55 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1932 : NodeCoverage93 [21,16,16] 16 40 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1933 : NodeCoverage93 [21,16,15] 15 41 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1934 : NodeCoverage93 [21,16,14] 14 42 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1935 : NodeCoverage93 [21,16,13] 13 43 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1936 : NodeCoverage93 [21,16,12] 12 44 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1937 : NodeCoverage93 [21,16,11] 11 45 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1938 : NodeCoverage93 [21,16,10] 10 46 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1939 : NodeCoverage93 [21,16,9] 9 47 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1940 : NodeCoverage93 [21,16,8] 8 48 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1941 : NodeCoverage93 [21,16,7] 7 49 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1942 : NodeCoverage93 [21,16,6] 6 50 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1943 : NodeCoverage93 [21,16,5] 5 51 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1944 : NodeCoverage93 [21,16,3] 3 53 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1945 : NodeCoverage93 [21,16] 16 56 :=
  node_fork93 (B := [16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1932
    (ChildrenCoverage93.cons _ _ compact93_node_1933
    (ChildrenCoverage93.cons _ _ compact93_node_1934
    (ChildrenCoverage93.cons _ _ compact93_node_1935
    (ChildrenCoverage93.cons _ _ compact93_node_1936
    (ChildrenCoverage93.cons _ _ compact93_node_1937
    (ChildrenCoverage93.cons _ _ compact93_node_1938
    (ChildrenCoverage93.cons _ _ compact93_node_1939
    (ChildrenCoverage93.cons _ _ compact93_node_1940
    (ChildrenCoverage93.cons _ _ compact93_node_1941
    (ChildrenCoverage93.cons _ _ compact93_node_1942
    (ChildrenCoverage93.cons _ _ compact93_node_1943
    (ChildrenCoverage93.cons _ _ compact93_node_1944
    ChildrenCoverage93.nil)))))))))))))

theorem compact93_node_1946 : NodeCoverage93 [21,15,15] 15 42 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1947 : NodeCoverage93 [21,15,14] 14 43 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1948 : NodeCoverage93 [21,15,13] 13 44 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1949 : NodeCoverage93 [21,15,12] 12 45 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
