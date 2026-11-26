module
public import Symconf93.CoverageShard93_051

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1856 : NodeCoverage93 [21,21,21,12] 12 18 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1857 : NodeCoverage93 [21,21,21,11] 11 19 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1858 : NodeCoverage93 [21,21,21,10] 10 20 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1859 : NodeCoverage93 [21,21,21,9] 9 21 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1860 : NodeCoverage93 [21,21,21,8] 8 22 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1861 : NodeCoverage93 [21,21,21,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1862 : NodeCoverage93 [21,21,21,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1863 : NodeCoverage93 [21,21,21,7,7,7,3,3,3] 3 0 :=
  node_no_weak_demand93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1864 : NodeCoverage93 [21,21,21,7,7,7,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1863
    ChildrenCoverage93.nil)

theorem compact93_node_1865 : NodeCoverage93 [21,21,21,7,7,7,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1864
    ChildrenCoverage93.nil)

theorem compact93_node_1866 : NodeCoverage93 [21,21,21,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1861
    (ChildrenCoverage93.cons _ _ compact93_node_1862
    (ChildrenCoverage93.cons _ _ compact93_node_1865
    ChildrenCoverage93.nil)))

theorem compact93_node_1867 : NodeCoverage93 [21,21,21,7,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1868 : NodeCoverage93 [21,21,21,7,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1869 : NodeCoverage93 [21,21,21,7,7,3,3,3,3] 3 4 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact93_node_1870 : NodeCoverage93 [21,21,21,7,7,3,3,3] 3 7 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1869
    ChildrenCoverage93.nil)

theorem compact93_node_1871 : NodeCoverage93 [21,21,21,7,7,3,3] 3 10 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1870
    ChildrenCoverage93.nil)

theorem compact93_node_1872 : NodeCoverage93 [21,21,21,7,7,3] 3 13 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1871
    ChildrenCoverage93.nil)

theorem compact93_node_1873 : NodeCoverage93 [21,21,21,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1866
    (ChildrenCoverage93.cons _ _ compact93_node_1867
    (ChildrenCoverage93.cons _ _ compact93_node_1868
    (ChildrenCoverage93.cons _ _ compact93_node_1872
    ChildrenCoverage93.nil))))

theorem compact93_node_1874 : NodeCoverage93 [21,21,21,7,6] 6 17 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1875 : NodeCoverage93 [21,21,21,7,5] 5 18 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1876 : NodeCoverage93 [21,21,21,7,3] 3 20 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1877 : NodeCoverage93 [21,21,21,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1873
    (ChildrenCoverage93.cons _ _ compact93_node_1874
    (ChildrenCoverage93.cons _ _ compact93_node_1875
    (ChildrenCoverage93.cons _ _ compact93_node_1876
    ChildrenCoverage93.nil))))

theorem compact93_node_1878 : NodeCoverage93 [21,21,21,6] 6 24 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1879 : NodeCoverage93 [21,21,21,5] 5 25 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1880 : NodeCoverage93 [21,21,21,3] 3 27 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1881 : NodeCoverage93 [21,21,21] 21 30 :=
  node_fork93 (B := [21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1847
    (ChildrenCoverage93.cons _ _ compact93_node_1848
    (ChildrenCoverage93.cons _ _ compact93_node_1849
    (ChildrenCoverage93.cons _ _ compact93_node_1850
    (ChildrenCoverage93.cons _ _ compact93_node_1851
    (ChildrenCoverage93.cons _ _ compact93_node_1852
    (ChildrenCoverage93.cons _ _ compact93_node_1853
    (ChildrenCoverage93.cons _ _ compact93_node_1854
    (ChildrenCoverage93.cons _ _ compact93_node_1855
    (ChildrenCoverage93.cons _ _ compact93_node_1856
    (ChildrenCoverage93.cons _ _ compact93_node_1857
    (ChildrenCoverage93.cons _ _ compact93_node_1858
    (ChildrenCoverage93.cons _ _ compact93_node_1859
    (ChildrenCoverage93.cons _ _ compact93_node_1860
    (ChildrenCoverage93.cons _ _ compact93_node_1877
    (ChildrenCoverage93.cons _ _ compact93_node_1878
    (ChildrenCoverage93.cons _ _ compact93_node_1879
    (ChildrenCoverage93.cons _ _ compact93_node_1880
    ChildrenCoverage93.nil))))))))))))))))))

theorem compact93_node_1882 : NodeCoverage93 [21,21,20] 20 31 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1883 : NodeCoverage93 [21,21,19] 19 32 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1884 : NodeCoverage93 [21,21,18] 18 33 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1885 : NodeCoverage93 [21,21,17] 17 34 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1886 : NodeCoverage93 [21,21,16] 16 35 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1887 : NodeCoverage93 [21,21,15] 15 36 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1888 : NodeCoverage93 [21,21,14] 14 37 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1889 : NodeCoverage93 [21,21,13] 13 38 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1890 : NodeCoverage93 [21,21,12] 12 39 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1891 : NodeCoverage93 [21,21,11] 11 40 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1892 : NodeCoverage93 [21,21,10] 10 41 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1893 : NodeCoverage93 [21,21,9] 9 42 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1894 : NodeCoverage93 [21,21,8] 8 43 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1895 : NodeCoverage93 [21,21,7,7,7,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1896 : NodeCoverage93 [21,21,7,7,7,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1897 : NodeCoverage93 [21,21,7,7,7,7,7,7,3,3,3] 3 0 :=
  node_no_weak_demand93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1898 : NodeCoverage93 [21,21,7,7,7,7,7,7,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1897
    ChildrenCoverage93.nil)

theorem compact93_node_1899 : NodeCoverage93 [21,21,7,7,7,7,7,7,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1898
    ChildrenCoverage93.nil)

theorem compact93_node_1900 : NodeCoverage93 [21,21,7,7,7,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1895
    (ChildrenCoverage93.cons _ _ compact93_node_1896
    (ChildrenCoverage93.cons _ _ compact93_node_1899
    ChildrenCoverage93.nil)))

theorem compact93_node_1901 : NodeCoverage93 [21,21,7,7,7,7,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1902 : NodeCoverage93 [21,21,7,7,7,7,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1903 : NodeCoverage93 [21,21,7,7,7,7,7,3,3,3,3] 3 4 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact93_node_1904 : NodeCoverage93 [21,21,7,7,7,7,7,3,3,3] 3 7 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1903
    ChildrenCoverage93.nil)

theorem compact93_node_1905 : NodeCoverage93 [21,21,7,7,7,7,7,3,3] 3 10 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1904
    ChildrenCoverage93.nil)

theorem compact93_node_1906 : NodeCoverage93 [21,21,7,7,7,7,7,3] 3 13 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1905
    ChildrenCoverage93.nil)

theorem compact93_node_1907 : NodeCoverage93 [21,21,7,7,7,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1900
    (ChildrenCoverage93.cons _ _ compact93_node_1901
    (ChildrenCoverage93.cons _ _ compact93_node_1902
    (ChildrenCoverage93.cons _ _ compact93_node_1906
    ChildrenCoverage93.nil))))

theorem compact93_node_1908 : NodeCoverage93 [21,21,7,7,7,7,6] 6 17 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1909 : NodeCoverage93 [21,21,7,7,7,7,5] 5 18 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1910 : NodeCoverage93 [21,21,7,7,7,7,3] 3 20 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1911 : NodeCoverage93 [21,21,7,7,7,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1907
    (ChildrenCoverage93.cons _ _ compact93_node_1908
    (ChildrenCoverage93.cons _ _ compact93_node_1909
    (ChildrenCoverage93.cons _ _ compact93_node_1910
    ChildrenCoverage93.nil))))

theorem compact93_node_1912 : NodeCoverage93 [21,21,7,7,7,6] 6 24 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1913 : NodeCoverage93 [21,21,7,7,7,5] 5 25 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1914 : NodeCoverage93 [21,21,7,7,7,3] 3 27 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
