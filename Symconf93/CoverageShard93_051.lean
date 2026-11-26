module
public import Symconf93.CoverageShard93_050

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1781 : NodeCoverage93 [22,22,22,15] 15 12 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1782 : NodeCoverage93 [22,22,22,14] 14 13 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1783 : NodeCoverage93 [22,22,22,13] 13 14 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1784 : NodeCoverage93 [22,22,22,12] 12 15 :=
  demand_node_prune93 12 compact93_demands_12 compact93_demands_12_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1785 : NodeCoverage93 [22,22,22,11,11,5] 5 0 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1786 : NodeCoverage93 [22,22,22,11,11] 11 5 :=
  node_fork93 (B := [5]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1785
    ChildrenCoverage93.nil)

theorem compact93_node_1787 : NodeCoverage93 [22,22,22,11,10] 10 6 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1788 : NodeCoverage93 [22,22,22,11,9] 9 7 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1789 : NodeCoverage93 [22,22,22,11,8] 8 8 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1790 : NodeCoverage93 [22,22,22,11,7] 7 9 :=
  demand_node_prune93 7 compact93_demands_07 compact93_demands_07_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1791 : NodeCoverage93 [22,22,22,11,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1792 : NodeCoverage93 [22,22,22,11,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1793 : NodeCoverage93 [22,22,22,11,3] 3 13 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1794 : NodeCoverage93 [22,22,22,11] 11 16 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1786
    (ChildrenCoverage93.cons _ _ compact93_node_1787
    (ChildrenCoverage93.cons _ _ compact93_node_1788
    (ChildrenCoverage93.cons _ _ compact93_node_1789
    (ChildrenCoverage93.cons _ _ compact93_node_1790
    (ChildrenCoverage93.cons _ _ compact93_node_1791
    (ChildrenCoverage93.cons _ _ compact93_node_1792
    (ChildrenCoverage93.cons _ _ compact93_node_1793
    ChildrenCoverage93.nil))))))))

theorem compact93_node_1795 : NodeCoverage93 [22,22,22,10] 10 17 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1796 : NodeCoverage93 [22,22,22,9] 9 18 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1797 : NodeCoverage93 [22,22,22,8] 8 19 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1798 : NodeCoverage93 [22,22,22,7] 7 20 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1799 : NodeCoverage93 [22,22,22,6] 6 21 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1800 : NodeCoverage93 [22,22,22,5] 5 22 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1801 : NodeCoverage93 [22,22,22,3] 3 24 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1802 : NodeCoverage93 [22,22,22] 22 27 :=
  node_fork93 (B := [22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1774
    (ChildrenCoverage93.cons _ _ compact93_node_1775
    (ChildrenCoverage93.cons _ _ compact93_node_1776
    (ChildrenCoverage93.cons _ _ compact93_node_1777
    (ChildrenCoverage93.cons _ _ compact93_node_1778
    (ChildrenCoverage93.cons _ _ compact93_node_1779
    (ChildrenCoverage93.cons _ _ compact93_node_1780
    (ChildrenCoverage93.cons _ _ compact93_node_1781
    (ChildrenCoverage93.cons _ _ compact93_node_1782
    (ChildrenCoverage93.cons _ _ compact93_node_1783
    (ChildrenCoverage93.cons _ _ compact93_node_1784
    (ChildrenCoverage93.cons _ _ compact93_node_1794
    (ChildrenCoverage93.cons _ _ compact93_node_1795
    (ChildrenCoverage93.cons _ _ compact93_node_1796
    (ChildrenCoverage93.cons _ _ compact93_node_1797
    (ChildrenCoverage93.cons _ _ compact93_node_1798
    (ChildrenCoverage93.cons _ _ compact93_node_1799
    (ChildrenCoverage93.cons _ _ compact93_node_1800
    (ChildrenCoverage93.cons _ _ compact93_node_1801
    ChildrenCoverage93.nil)))))))))))))))))))

theorem compact93_node_1803 : NodeCoverage93 [22,22,21] 21 28 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1804 : NodeCoverage93 [22,22,20] 20 29 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1805 : NodeCoverage93 [22,22,19] 19 30 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1806 : NodeCoverage93 [22,22,18] 18 31 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1807 : NodeCoverage93 [22,22,17] 17 32 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1808 : NodeCoverage93 [22,22,16] 16 33 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1809 : NodeCoverage93 [22,22,15] 15 34 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1810 : NodeCoverage93 [22,22,14] 14 35 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1811 : NodeCoverage93 [22,22,13] 13 36 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1812 : NodeCoverage93 [22,22,12] 12 37 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1813 : NodeCoverage93 [22,22,11] 11 38 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1814 : NodeCoverage93 [22,22,10] 10 39 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1815 : NodeCoverage93 [22,22,9] 9 40 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1816 : NodeCoverage93 [22,22,8] 8 41 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1817 : NodeCoverage93 [22,22,7] 7 42 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1818 : NodeCoverage93 [22,22,6] 6 43 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1819 : NodeCoverage93 [22,22,5] 5 44 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1820 : NodeCoverage93 [22,22,3] 3 46 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1821 : NodeCoverage93 [22,22] 22 49 :=
  node_fork93 (B := [22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1802
    (ChildrenCoverage93.cons _ _ compact93_node_1803
    (ChildrenCoverage93.cons _ _ compact93_node_1804
    (ChildrenCoverage93.cons _ _ compact93_node_1805
    (ChildrenCoverage93.cons _ _ compact93_node_1806
    (ChildrenCoverage93.cons _ _ compact93_node_1807
    (ChildrenCoverage93.cons _ _ compact93_node_1808
    (ChildrenCoverage93.cons _ _ compact93_node_1809
    (ChildrenCoverage93.cons _ _ compact93_node_1810
    (ChildrenCoverage93.cons _ _ compact93_node_1811
    (ChildrenCoverage93.cons _ _ compact93_node_1812
    (ChildrenCoverage93.cons _ _ compact93_node_1813
    (ChildrenCoverage93.cons _ _ compact93_node_1814
    (ChildrenCoverage93.cons _ _ compact93_node_1815
    (ChildrenCoverage93.cons _ _ compact93_node_1816
    (ChildrenCoverage93.cons _ _ compact93_node_1817
    (ChildrenCoverage93.cons _ _ compact93_node_1818
    (ChildrenCoverage93.cons _ _ compact93_node_1819
    (ChildrenCoverage93.cons _ _ compact93_node_1820
    ChildrenCoverage93.nil)))))))))))))))))))

theorem compact93_node_1822 : NodeCoverage93 [22,21] 21 50 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1823 : NodeCoverage93 [22,20] 20 51 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1824 : NodeCoverage93 [22,19] 19 52 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1825 : NodeCoverage93 [22,18] 18 53 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1826 : NodeCoverage93 [22,17] 17 54 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1827 : NodeCoverage93 [22,16] 16 55 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1828 : NodeCoverage93 [22,15] 15 56 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1829 : NodeCoverage93 [22,14] 14 57 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1830 : NodeCoverage93 [22,13] 13 58 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1831 : NodeCoverage93 [22,12] 12 59 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1832 : NodeCoverage93 [22,11] 11 60 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1833 : NodeCoverage93 [22,10] 10 61 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1834 : NodeCoverage93 [22,9] 9 62 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1835 : NodeCoverage93 [22,8] 8 63 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1836 : NodeCoverage93 [22,7] 7 64 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1837 : NodeCoverage93 [22,6] 6 65 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1838 : NodeCoverage93 [22,5] 5 66 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1839 : NodeCoverage93 [22,3] 3 68 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1840 : NodeCoverage93 [22] 22 71 :=
  node_fork93 (B := [22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1821
    (ChildrenCoverage93.cons _ _ compact93_node_1822
    (ChildrenCoverage93.cons _ _ compact93_node_1823
    (ChildrenCoverage93.cons _ _ compact93_node_1824
    (ChildrenCoverage93.cons _ _ compact93_node_1825
    (ChildrenCoverage93.cons _ _ compact93_node_1826
    (ChildrenCoverage93.cons _ _ compact93_node_1827
    (ChildrenCoverage93.cons _ _ compact93_node_1828
    (ChildrenCoverage93.cons _ _ compact93_node_1829
    (ChildrenCoverage93.cons _ _ compact93_node_1830
    (ChildrenCoverage93.cons _ _ compact93_node_1831
    (ChildrenCoverage93.cons _ _ compact93_node_1832
    (ChildrenCoverage93.cons _ _ compact93_node_1833
    (ChildrenCoverage93.cons _ _ compact93_node_1834
    (ChildrenCoverage93.cons _ _ compact93_node_1835
    (ChildrenCoverage93.cons _ _ compact93_node_1836
    (ChildrenCoverage93.cons _ _ compact93_node_1837
    (ChildrenCoverage93.cons _ _ compact93_node_1838
    (ChildrenCoverage93.cons _ _ compact93_node_1839
    ChildrenCoverage93.nil)))))))))))))))))))

theorem compact93_node_1841 : NodeCoverage93 [21,21,21,21,9] 9 0 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1842 : NodeCoverage93 [21,21,21,21,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1843 : NodeCoverage93 [21,21,21,21,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1844 : NodeCoverage93 [21,21,21,21,3,3,3] 3 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_1845 : NodeCoverage93 [21,21,21,21,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1844
    ChildrenCoverage93.nil)

theorem compact93_node_1846 : NodeCoverage93 [21,21,21,21,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1845
    ChildrenCoverage93.nil)

theorem compact93_node_1847 : NodeCoverage93 [21,21,21,21] 21 9 :=
  node_fork93 (B := [9,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1841
    (ChildrenCoverage93.cons _ _ compact93_node_1842
    (ChildrenCoverage93.cons _ _ compact93_node_1843
    (ChildrenCoverage93.cons _ _ compact93_node_1846
    ChildrenCoverage93.nil))))

theorem compact93_node_1848 : NodeCoverage93 [21,21,21,20] 20 10 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1849 : NodeCoverage93 [21,21,21,19] 19 11 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1850 : NodeCoverage93 [21,21,21,18] 18 12 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1851 : NodeCoverage93 [21,21,21,17] 17 13 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1852 : NodeCoverage93 [21,21,21,16] 16 14 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1853 : NodeCoverage93 [21,21,21,15] 15 15 :=
  demand_node_prune93 15 compact93_demands_15 compact93_demands_15_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1854 : NodeCoverage93 [21,21,21,14] 14 16 :=
  demand_node_prune93 14 compact93_demands_14 compact93_demands_14_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1855 : NodeCoverage93 [21,21,21,13] 13 17 :=
  demand_node_prune93 13 compact93_demands_13 compact93_demands_13_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
