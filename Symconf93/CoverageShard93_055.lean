module
public import Symconf93.CoverageShard93_054

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_1983 : NodeCoverage93 [21,11,9] 9 52 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1984 : NodeCoverage93 [21,11,8] 8 53 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1985 : NodeCoverage93 [21,11,7] 7 54 :=
  demand_node_prune93 11 compact93_demands_11 compact93_demands_11_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1986 : NodeCoverage93 [21,11,6] 6 55 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1987 : NodeCoverage93 [21,11,5] 5 56 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1988 : NodeCoverage93 [21,11,3] 3 58 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1989 : NodeCoverage93 [21,11] 11 61 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1981
    (ChildrenCoverage93.cons _ _ compact93_node_1982
    (ChildrenCoverage93.cons _ _ compact93_node_1983
    (ChildrenCoverage93.cons _ _ compact93_node_1984
    (ChildrenCoverage93.cons _ _ compact93_node_1985
    (ChildrenCoverage93.cons _ _ compact93_node_1986
    (ChildrenCoverage93.cons _ _ compact93_node_1987
    (ChildrenCoverage93.cons _ _ compact93_node_1988
    ChildrenCoverage93.nil))))))))

theorem compact93_node_1990 : NodeCoverage93 [21,10,10] 10 52 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1991 : NodeCoverage93 [21,10,9] 9 53 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1992 : NodeCoverage93 [21,10,8] 8 54 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1993 : NodeCoverage93 [21,10,7] 7 55 :=
  demand_node_prune93 10 compact93_demands_10 compact93_demands_10_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1994 : NodeCoverage93 [21,10,6] 6 56 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1995 : NodeCoverage93 [21,10,5] 5 57 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1996 : NodeCoverage93 [21,10,3] 3 59 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1997 : NodeCoverage93 [21,10] 10 62 :=
  node_fork93 (B := [10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1990
    (ChildrenCoverage93.cons _ _ compact93_node_1991
    (ChildrenCoverage93.cons _ _ compact93_node_1992
    (ChildrenCoverage93.cons _ _ compact93_node_1993
    (ChildrenCoverage93.cons _ _ compact93_node_1994
    (ChildrenCoverage93.cons _ _ compact93_node_1995
    (ChildrenCoverage93.cons _ _ compact93_node_1996
    ChildrenCoverage93.nil)))))))

theorem compact93_node_1998 : NodeCoverage93 [21,9,9] 9 54 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_1999 : NodeCoverage93 [21,9,8] 8 55 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2000 : NodeCoverage93 [21,9,7] 7 56 :=
  demand_node_prune93 9 compact93_demands_09 compact93_demands_09_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2001 : NodeCoverage93 [21,9,6] 6 57 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2002 : NodeCoverage93 [21,9,5] 5 58 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2003 : NodeCoverage93 [21,9,3] 3 60 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2004 : NodeCoverage93 [21,9] 9 63 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_1998
    (ChildrenCoverage93.cons _ _ compact93_node_1999
    (ChildrenCoverage93.cons _ _ compact93_node_2000
    (ChildrenCoverage93.cons _ _ compact93_node_2001
    (ChildrenCoverage93.cons _ _ compact93_node_2002
    (ChildrenCoverage93.cons _ _ compact93_node_2003
    ChildrenCoverage93.nil))))))

theorem compact93_node_2005 : NodeCoverage93 [21,8] 8 64 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2006 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,7,6] 6 3 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2007 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,7,5] 5 4 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2008 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,7,3,3,3] 3 0 :=
  node_no_weak_demand93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2009 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,7,3,3] 3 3 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2008
    ChildrenCoverage93.nil)

theorem compact93_node_2010 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,7,3] 3 6 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2009
    ChildrenCoverage93.nil)

theorem compact93_node_2011 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,7] 7 9 :=
  node_fork93 (B := [6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2006
    (ChildrenCoverage93.cons _ _ compact93_node_2007
    (ChildrenCoverage93.cons _ _ compact93_node_2010
    ChildrenCoverage93.nil)))

theorem compact93_node_2012 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,6] 6 10 :=
  demand_node_prune93 6 compact93_demands_06 compact93_demands_06_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2013 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,5] 5 11 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2014 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,3,3,3,3] 3 4 :=
  node_fork93 (B := []) (by decide +kernel) (by decide +kernel)
    ChildrenCoverage93.nil

theorem compact93_node_2015 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,3,3,3] 3 7 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2014
    ChildrenCoverage93.nil)

theorem compact93_node_2016 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,3,3] 3 10 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2015
    ChildrenCoverage93.nil)

theorem compact93_node_2017 : NodeCoverage93 [21,7,7,7,7,7,7,7,7,3] 3 13 :=
  node_fork93 (B := [3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2016
    ChildrenCoverage93.nil)

theorem compact93_node_2018 : NodeCoverage93 [21,7,7,7,7,7,7,7,7] 7 16 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2011
    (ChildrenCoverage93.cons _ _ compact93_node_2012
    (ChildrenCoverage93.cons _ _ compact93_node_2013
    (ChildrenCoverage93.cons _ _ compact93_node_2017
    ChildrenCoverage93.nil))))

theorem compact93_node_2019 : NodeCoverage93 [21,7,7,7,7,7,7,7,6] 6 17 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2020 : NodeCoverage93 [21,7,7,7,7,7,7,7,5] 5 18 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2021 : NodeCoverage93 [21,7,7,7,7,7,7,7,3] 3 20 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2022 : NodeCoverage93 [21,7,7,7,7,7,7,7] 7 23 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2018
    (ChildrenCoverage93.cons _ _ compact93_node_2019
    (ChildrenCoverage93.cons _ _ compact93_node_2020
    (ChildrenCoverage93.cons _ _ compact93_node_2021
    ChildrenCoverage93.nil))))

theorem compact93_node_2023 : NodeCoverage93 [21,7,7,7,7,7,7,6] 6 24 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2024 : NodeCoverage93 [21,7,7,7,7,7,7,5] 5 25 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2025 : NodeCoverage93 [21,7,7,7,7,7,7,3] 3 27 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2026 : NodeCoverage93 [21,7,7,7,7,7,7] 7 30 :=
  node_fork93 (B := [7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_2022
    (ChildrenCoverage93.cons _ _ compact93_node_2023
    (ChildrenCoverage93.cons _ _ compact93_node_2024
    (ChildrenCoverage93.cons _ _ compact93_node_2025
    ChildrenCoverage93.nil))))

theorem compact93_node_2027 : NodeCoverage93 [21,7,7,7,7,7,6] 6 31 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_2028 : NodeCoverage93 [21,7,7,7,7,7,5] 5 32 :=
  demand_node_prune93 21 compact93_demands_21 compact93_demands_21_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
