module
public import Symconf93.CoverageShard93_049

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1706 : NodeCoverage93 [24,9,5] 5 55 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1707 : NodeCoverage93 [24,9,3] 3 57 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1708 : NodeCoverage93 [24,9] 9 60 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1702
    (ChildrenCoverage93.cons _ _ compact93_node_1703
    (ChildrenCoverage93.cons _ _ compact93_node_1704
    (ChildrenCoverage93.cons _ _ compact93_node_1705
    (ChildrenCoverage93.cons _ _ compact93_node_1706
    (ChildrenCoverage93.cons _ _ compact93_node_1707
    ChildrenCoverage93.nil))))))

theorem compact93_node_1709 : NodeCoverage93 [24,8] 8 61 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1710 : NodeCoverage93 [24,7] 7 62 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1711 : NodeCoverage93 [24,6] 6 63 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1712 : NodeCoverage93 [24,5] 5 64 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1713 : NodeCoverage93 [24,3] 3 66 :=
  demand_node_prune93 24 compact93_demands_24 compact93_demands_24_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1714 : NodeCoverage93 [24] 24 69 :=
  node_fork93 (B := [24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1607
    (ChildrenCoverage93.cons _ _ compact93_node_1608
    (ChildrenCoverage93.cons _ _ compact93_node_1609
    (ChildrenCoverage93.cons _ _ compact93_node_1610
    (ChildrenCoverage93.cons _ _ compact93_node_1611
    (ChildrenCoverage93.cons _ _ compact93_node_1612
    (ChildrenCoverage93.cons _ _ compact93_node_1613
    (ChildrenCoverage93.cons _ _ compact93_node_1614
    (ChildrenCoverage93.cons _ _ compact93_node_1615
    (ChildrenCoverage93.cons _ _ compact93_node_1616
    (ChildrenCoverage93.cons _ _ compact93_node_1617
    (ChildrenCoverage93.cons _ _ compact93_node_1628
    (ChildrenCoverage93.cons _ _ compact93_node_1684
    (ChildrenCoverage93.cons _ _ compact93_node_1693
    (ChildrenCoverage93.cons _ _ compact93_node_1701
    (ChildrenCoverage93.cons _ _ compact93_node_1708
    (ChildrenCoverage93.cons _ _ compact93_node_1709
    (ChildrenCoverage93.cons _ _ compact93_node_1710
    (ChildrenCoverage93.cons _ _ compact93_node_1711
    (ChildrenCoverage93.cons _ _ compact93_node_1712
    (ChildrenCoverage93.cons _ _ compact93_node_1713
    ChildrenCoverage93.nil)))))))))))))))))))))

theorem compact93_node_1715 : NodeCoverage93 [23,23,23,21] 21 3 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1716 : NodeCoverage93 [23,23,23,20] 20 4 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1717 : NodeCoverage93 [23,23,23,19] 19 5 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1718 : NodeCoverage93 [23,23,23,18] 18 6 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1719 : NodeCoverage93 [23,23,23,17] 17 7 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1720 : NodeCoverage93 [23,23,23,16] 16 8 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1721 : NodeCoverage93 [23,23,23,15] 15 9 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1722 : NodeCoverage93 [23,23,23,14] 14 10 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1723 : NodeCoverage93 [23,23,23,13] 13 11 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1724 : NodeCoverage93 [23,23,23,12] 12 12 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1725 : NodeCoverage93 [23,23,23,11] 11 13 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1726 : NodeCoverage93 [23,23,23,10] 10 14 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1727 : NodeCoverage93 [23,23,23,9] 9 15 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1728 : NodeCoverage93 [23,23,23,8] 8 16 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1729 : NodeCoverage93 [23,23,23,7] 7 17 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1730 : NodeCoverage93 [23,23,23,6] 6 18 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1731 : NodeCoverage93 [23,23,23,5] 5 19 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1732 : NodeCoverage93 [23,23,23,3] 3 21 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1733 : NodeCoverage93 [23,23,23] 23 24 :=
  node_fork93 (B := [21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1715
    (ChildrenCoverage93.cons _ _ compact93_node_1716
    (ChildrenCoverage93.cons _ _ compact93_node_1717
    (ChildrenCoverage93.cons _ _ compact93_node_1718
    (ChildrenCoverage93.cons _ _ compact93_node_1719
    (ChildrenCoverage93.cons _ _ compact93_node_1720
    (ChildrenCoverage93.cons _ _ compact93_node_1721
    (ChildrenCoverage93.cons _ _ compact93_node_1722
    (ChildrenCoverage93.cons _ _ compact93_node_1723
    (ChildrenCoverage93.cons _ _ compact93_node_1724
    (ChildrenCoverage93.cons _ _ compact93_node_1725
    (ChildrenCoverage93.cons _ _ compact93_node_1726
    (ChildrenCoverage93.cons _ _ compact93_node_1727
    (ChildrenCoverage93.cons _ _ compact93_node_1728
    (ChildrenCoverage93.cons _ _ compact93_node_1729
    (ChildrenCoverage93.cons _ _ compact93_node_1730
    (ChildrenCoverage93.cons _ _ compact93_node_1731
    (ChildrenCoverage93.cons _ _ compact93_node_1732
    ChildrenCoverage93.nil))))))))))))))))))

theorem compact93_node_1734 : NodeCoverage93 [23,23,22] 22 25 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1735 : NodeCoverage93 [23,23,21] 21 26 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1736 : NodeCoverage93 [23,23,20] 20 27 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1737 : NodeCoverage93 [23,23,19] 19 28 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1738 : NodeCoverage93 [23,23,18] 18 29 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1739 : NodeCoverage93 [23,23,17] 17 30 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1740 : NodeCoverage93 [23,23,16] 16 31 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1741 : NodeCoverage93 [23,23,15] 15 32 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1742 : NodeCoverage93 [23,23,14] 14 33 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1743 : NodeCoverage93 [23,23,13] 13 34 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1744 : NodeCoverage93 [23,23,12] 12 35 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1745 : NodeCoverage93 [23,23,11] 11 36 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1746 : NodeCoverage93 [23,23,10] 10 37 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1747 : NodeCoverage93 [23,23,9] 9 38 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1748 : NodeCoverage93 [23,23,8] 8 39 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1749 : NodeCoverage93 [23,23,7] 7 40 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1750 : NodeCoverage93 [23,23,6] 6 41 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1751 : NodeCoverage93 [23,23,5] 5 42 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1752 : NodeCoverage93 [23,23,3] 3 44 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1753 : NodeCoverage93 [23,23] 23 47 :=
  node_fork93 (B := [23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1733
    (ChildrenCoverage93.cons _ _ compact93_node_1734
    (ChildrenCoverage93.cons _ _ compact93_node_1735
    (ChildrenCoverage93.cons _ _ compact93_node_1736
    (ChildrenCoverage93.cons _ _ compact93_node_1737
    (ChildrenCoverage93.cons _ _ compact93_node_1738
    (ChildrenCoverage93.cons _ _ compact93_node_1739
    (ChildrenCoverage93.cons _ _ compact93_node_1740
    (ChildrenCoverage93.cons _ _ compact93_node_1741
    (ChildrenCoverage93.cons _ _ compact93_node_1742
    (ChildrenCoverage93.cons _ _ compact93_node_1743
    (ChildrenCoverage93.cons _ _ compact93_node_1744
    (ChildrenCoverage93.cons _ _ compact93_node_1745
    (ChildrenCoverage93.cons _ _ compact93_node_1746
    (ChildrenCoverage93.cons _ _ compact93_node_1747
    (ChildrenCoverage93.cons _ _ compact93_node_1748
    (ChildrenCoverage93.cons _ _ compact93_node_1749
    (ChildrenCoverage93.cons _ _ compact93_node_1750
    (ChildrenCoverage93.cons _ _ compact93_node_1751
    (ChildrenCoverage93.cons _ _ compact93_node_1752
    ChildrenCoverage93.nil))))))))))))))))))))

theorem compact93_node_1754 : NodeCoverage93 [23,22] 22 48 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1755 : NodeCoverage93 [23,21] 21 49 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1756 : NodeCoverage93 [23,20] 20 50 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1757 : NodeCoverage93 [23,19] 19 51 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1758 : NodeCoverage93 [23,18] 18 52 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1759 : NodeCoverage93 [23,17] 17 53 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1760 : NodeCoverage93 [23,16] 16 54 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1761 : NodeCoverage93 [23,15] 15 55 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1762 : NodeCoverage93 [23,14] 14 56 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1763 : NodeCoverage93 [23,13] 13 57 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1764 : NodeCoverage93 [23,12] 12 58 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1765 : NodeCoverage93 [23,11] 11 59 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1766 : NodeCoverage93 [23,10] 10 60 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1767 : NodeCoverage93 [23,9] 9 61 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1768 : NodeCoverage93 [23,8] 8 62 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1769 : NodeCoverage93 [23,7] 7 63 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1770 : NodeCoverage93 [23,6] 6 64 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1771 : NodeCoverage93 [23,5] 5 65 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1772 : NodeCoverage93 [23,3] 3 67 :=
  demand_node_prune93 23 compact93_demands_23 compact93_demands_23_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1773 : NodeCoverage93 [23] 23 70 :=
  node_fork93 (B := [23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1753
    (ChildrenCoverage93.cons _ _ compact93_node_1754
    (ChildrenCoverage93.cons _ _ compact93_node_1755
    (ChildrenCoverage93.cons _ _ compact93_node_1756
    (ChildrenCoverage93.cons _ _ compact93_node_1757
    (ChildrenCoverage93.cons _ _ compact93_node_1758
    (ChildrenCoverage93.cons _ _ compact93_node_1759
    (ChildrenCoverage93.cons _ _ compact93_node_1760
    (ChildrenCoverage93.cons _ _ compact93_node_1761
    (ChildrenCoverage93.cons _ _ compact93_node_1762
    (ChildrenCoverage93.cons _ _ compact93_node_1763
    (ChildrenCoverage93.cons _ _ compact93_node_1764
    (ChildrenCoverage93.cons _ _ compact93_node_1765
    (ChildrenCoverage93.cons _ _ compact93_node_1766
    (ChildrenCoverage93.cons _ _ compact93_node_1767
    (ChildrenCoverage93.cons _ _ compact93_node_1768
    (ChildrenCoverage93.cons _ _ compact93_node_1769
    (ChildrenCoverage93.cons _ _ compact93_node_1770
    (ChildrenCoverage93.cons _ _ compact93_node_1771
    (ChildrenCoverage93.cons _ _ compact93_node_1772
    ChildrenCoverage93.nil))))))))))))))))))))

theorem compact93_node_1774 : NodeCoverage93 [22,22,22,22] 22 5 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1775 : NodeCoverage93 [22,22,22,21] 21 6 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1776 : NodeCoverage93 [22,22,22,20] 20 7 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1777 : NodeCoverage93 [22,22,22,19] 19 8 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1778 : NodeCoverage93 [22,22,22,18] 18 9 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1779 : NodeCoverage93 [22,22,22,17] 17 10 :=
  demand_node_prune93 22 compact93_demands_22 compact93_demands_22_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1780 : NodeCoverage93 [22,22,22,16] 16 11 :=
  demand_node_prune93 16 compact93_demands_16 compact93_demands_16_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
