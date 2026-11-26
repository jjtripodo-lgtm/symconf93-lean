module
public import Symconf93.CoverageParallelLow93_012

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact_parallel93_node_2611 : NodeCoverage93 [18,9,9,5] 5 52 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2612 : NodeCoverage93 [18,9,9,3] 3 54 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2613 : NodeCoverage93 [18,9,9] 9 57 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2607
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2608
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2609
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2610
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2611
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2612
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2614 : NodeCoverage93 [18,9,8] 8 58 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2615 : NodeCoverage93 [18,9,7] 7 59 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2616 : NodeCoverage93 [18,9,6] 6 60 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2617 : NodeCoverage93 [18,9,5] 5 61 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2618 : NodeCoverage93 [18,9,3] 3 63 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2619 : NodeCoverage93 [18,9] 9 66 :=
  node_fork93 (B := [9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2613
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2614
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2615
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2616
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2617
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2618
    ChildrenCoverage93.nil))))))

theorem compact_parallel93_node_2620 : NodeCoverage93 [18,8] 8 67 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2621 : NodeCoverage93 [18,7] 7 68 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2622 : NodeCoverage93 [18,6] 6 69 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2623 : NodeCoverage93 [18,5] 5 70 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2624 : NodeCoverage93 [18,3] 3 72 :=
  demand_node_prune93 18 compact93_demands_18 compact93_demands_18_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2625 : NodeCoverage93 [18] 18 75 :=
  node_fork93 (B := [18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2503
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2504
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2518
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2531
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2532
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2543
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2559
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2568
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2576
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2619
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2620
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2621
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2622
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2623
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2624
    ChildrenCoverage93.nil)))))))))))))))

theorem compact_parallel93_node_2626 : NodeCoverage93 [17,17,17,17,17,8] 8 0 :=
  demand_node_prune93 8 compact93_demands_08 compact93_demands_08_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2627 : NodeCoverage93 [17,17,17,17,17,5] 5 3 :=
  demand_node_prune93 5 compact93_demands_05 compact93_demands_05_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2628 : NodeCoverage93 [17,17,17,17,17,3] 3 5 :=
  demand_node_prune93 3 compact93_demands_03 compact93_demands_03_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2629 : NodeCoverage93 [17,17,17,17,17] 17 8 :=
  node_fork93 (B := [8,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2626
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2627
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2628
    ChildrenCoverage93.nil)))

theorem compact_parallel93_node_2630 : NodeCoverage93 [17,17,17,17,16] 16 9 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2631 : NodeCoverage93 [17,17,17,17,15] 15 10 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2632 : NodeCoverage93 [17,17,17,17,14] 14 11 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2633 : NodeCoverage93 [17,17,17,17,13] 13 12 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2634 : NodeCoverage93 [17,17,17,17,12] 12 13 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2635 : NodeCoverage93 [17,17,17,17,11] 11 14 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2636 : NodeCoverage93 [17,17,17,17,10] 10 15 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2637 : NodeCoverage93 [17,17,17,17,9] 9 16 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2638 : NodeCoverage93 [17,17,17,17,8] 8 17 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2639 : NodeCoverage93 [17,17,17,17,7] 7 18 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2640 : NodeCoverage93 [17,17,17,17,6] 6 19 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2641 : NodeCoverage93 [17,17,17,17,5] 5 20 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2642 : NodeCoverage93 [17,17,17,17,3] 3 22 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2643 : NodeCoverage93 [17,17,17,17] 17 25 :=
  node_fork93 (B := [17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2629
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2630
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2631
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2632
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2633
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2634
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2635
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2636
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2637
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2638
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2639
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2640
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2641
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2642
    ChildrenCoverage93.nil))))))))))))))

theorem compact_parallel93_node_2644 : NodeCoverage93 [17,17,17,16] 16 26 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2645 : NodeCoverage93 [17,17,17,15] 15 27 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2646 : NodeCoverage93 [17,17,17,14] 14 28 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2647 : NodeCoverage93 [17,17,17,13] 13 29 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2648 : NodeCoverage93 [17,17,17,12] 12 30 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2649 : NodeCoverage93 [17,17,17,11] 11 31 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2650 : NodeCoverage93 [17,17,17,10] 10 32 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2651 : NodeCoverage93 [17,17,17,9] 9 33 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2652 : NodeCoverage93 [17,17,17,8] 8 34 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2653 : NodeCoverage93 [17,17,17,7] 7 35 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2654 : NodeCoverage93 [17,17,17,6] 6 36 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2655 : NodeCoverage93 [17,17,17,5] 5 37 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2656 : NodeCoverage93 [17,17,17,3] 3 39 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2657 : NodeCoverage93 [17,17,17] 17 42 :=
  node_fork93 (B := [17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2643
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2644
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2645
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2646
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2647
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2648
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2649
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2650
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2651
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2652
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2653
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2654
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2655
    (ChildrenCoverage93.cons _ _ compact_parallel93_node_2656
    ChildrenCoverage93.nil))))))))))))))

theorem compact_parallel93_node_2658 : NodeCoverage93 [17,17,16] 16 43 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2659 : NodeCoverage93 [17,17,15] 15 44 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact_parallel93_node_2660 : NodeCoverage93 [17,17,14] 14 45 :=
  demand_node_prune93 17 compact93_demands_17 compact93_demands_17_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
