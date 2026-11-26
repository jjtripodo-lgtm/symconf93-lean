module
public import Symconf93.CoverageShard93_015

@[expose] public section

namespace Symconf93
set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem compact93_node_0902 : NodeCoverage93 [33,11,11,11,5] 5 22 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0903 : NodeCoverage93 [33,11,11,11,3] 3 24 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0904 : NodeCoverage93 [33,11,11,11] 11 27 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0896
    (ChildrenCoverage93.cons _ _ compact93_node_0897
    (ChildrenCoverage93.cons _ _ compact93_node_0898
    (ChildrenCoverage93.cons _ _ compact93_node_0899
    (ChildrenCoverage93.cons _ _ compact93_node_0900
    (ChildrenCoverage93.cons _ _ compact93_node_0901
    (ChildrenCoverage93.cons _ _ compact93_node_0902
    (ChildrenCoverage93.cons _ _ compact93_node_0903
    ChildrenCoverage93.nil))))))))

theorem compact93_node_0905 : NodeCoverage93 [33,11,11,10] 10 28 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0906 : NodeCoverage93 [33,11,11,9] 9 29 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0907 : NodeCoverage93 [33,11,11,8] 8 30 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0908 : NodeCoverage93 [33,11,11,7] 7 31 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0909 : NodeCoverage93 [33,11,11,6] 6 32 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0910 : NodeCoverage93 [33,11,11,5] 5 33 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0911 : NodeCoverage93 [33,11,11,3] 3 35 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0912 : NodeCoverage93 [33,11,11] 11 38 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0904
    (ChildrenCoverage93.cons _ _ compact93_node_0905
    (ChildrenCoverage93.cons _ _ compact93_node_0906
    (ChildrenCoverage93.cons _ _ compact93_node_0907
    (ChildrenCoverage93.cons _ _ compact93_node_0908
    (ChildrenCoverage93.cons _ _ compact93_node_0909
    (ChildrenCoverage93.cons _ _ compact93_node_0910
    (ChildrenCoverage93.cons _ _ compact93_node_0911
    ChildrenCoverage93.nil))))))))

theorem compact93_node_0913 : NodeCoverage93 [33,11,10] 10 39 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0914 : NodeCoverage93 [33,11,9] 9 40 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0915 : NodeCoverage93 [33,11,8] 8 41 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0916 : NodeCoverage93 [33,11,7] 7 42 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0917 : NodeCoverage93 [33,11,6] 6 43 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0918 : NodeCoverage93 [33,11,5] 5 44 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0919 : NodeCoverage93 [33,11,3] 3 46 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0920 : NodeCoverage93 [33,11] 11 49 :=
  node_fork93 (B := [11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0912
    (ChildrenCoverage93.cons _ _ compact93_node_0913
    (ChildrenCoverage93.cons _ _ compact93_node_0914
    (ChildrenCoverage93.cons _ _ compact93_node_0915
    (ChildrenCoverage93.cons _ _ compact93_node_0916
    (ChildrenCoverage93.cons _ _ compact93_node_0917
    (ChildrenCoverage93.cons _ _ compact93_node_0918
    (ChildrenCoverage93.cons _ _ compact93_node_0919
    ChildrenCoverage93.nil))))))))

theorem compact93_node_0921 : NodeCoverage93 [33,10] 10 50 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0922 : NodeCoverage93 [33,9] 9 51 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0923 : NodeCoverage93 [33,8] 8 52 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0924 : NodeCoverage93 [33,7] 7 53 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0925 : NodeCoverage93 [33,6] 6 54 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0926 : NodeCoverage93 [33,5] 5 55 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0927 : NodeCoverage93 [33,3] 3 57 :=
  demand_node_prune93 33 compact93_demands_33 compact93_demands_33_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0928 : NodeCoverage93 [33] 33 60 :=
  node_fork93 (B := [33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0865
    (ChildrenCoverage93.cons _ _ compact93_node_0866
    (ChildrenCoverage93.cons _ _ compact93_node_0867
    (ChildrenCoverage93.cons _ _ compact93_node_0868
    (ChildrenCoverage93.cons _ _ compact93_node_0869
    (ChildrenCoverage93.cons _ _ compact93_node_0870
    (ChildrenCoverage93.cons _ _ compact93_node_0871
    (ChildrenCoverage93.cons _ _ compact93_node_0872
    (ChildrenCoverage93.cons _ _ compact93_node_0873
    (ChildrenCoverage93.cons _ _ compact93_node_0874
    (ChildrenCoverage93.cons _ _ compact93_node_0875
    (ChildrenCoverage93.cons _ _ compact93_node_0876
    (ChildrenCoverage93.cons _ _ compact93_node_0877
    (ChildrenCoverage93.cons _ _ compact93_node_0878
    (ChildrenCoverage93.cons _ _ compact93_node_0879
    (ChildrenCoverage93.cons _ _ compact93_node_0880
    (ChildrenCoverage93.cons _ _ compact93_node_0881
    (ChildrenCoverage93.cons _ _ compact93_node_0882
    (ChildrenCoverage93.cons _ _ compact93_node_0883
    (ChildrenCoverage93.cons _ _ compact93_node_0884
    (ChildrenCoverage93.cons _ _ compact93_node_0885
    (ChildrenCoverage93.cons _ _ compact93_node_0886
    (ChildrenCoverage93.cons _ _ compact93_node_0920
    (ChildrenCoverage93.cons _ _ compact93_node_0921
    (ChildrenCoverage93.cons _ _ compact93_node_0922
    (ChildrenCoverage93.cons _ _ compact93_node_0923
    (ChildrenCoverage93.cons _ _ compact93_node_0924
    (ChildrenCoverage93.cons _ _ compact93_node_0925
    (ChildrenCoverage93.cons _ _ compact93_node_0926
    (ChildrenCoverage93.cons _ _ compact93_node_0927
    ChildrenCoverage93.nil))))))))))))))))))))))))))))))

theorem compact93_node_0929 : NodeCoverage93 [32] 32 61 :=
  demand_node_prune93 32 compact93_demands_32 compact93_demands_32_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0930 : NodeCoverage93 [31,31,31] 31 0 :=
  node_good_leaf93 (by decide +kernel)

theorem compact93_node_0931 : NodeCoverage93 [31,31,28] 28 3 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0932 : NodeCoverage93 [31,31,27] 27 4 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0933 : NodeCoverage93 [31,31,26] 26 5 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0934 : NodeCoverage93 [31,31,25] 25 6 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0935 : NodeCoverage93 [31,31,24] 24 7 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0936 : NodeCoverage93 [31,31,23] 23 8 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0937 : NodeCoverage93 [31,31,22] 22 9 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0938 : NodeCoverage93 [31,31,21] 21 10 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0939 : NodeCoverage93 [31,31,20] 20 11 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0940 : NodeCoverage93 [31,31,19] 19 12 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0941 : NodeCoverage93 [31,31,18] 18 13 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0942 : NodeCoverage93 [31,31,17] 17 14 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0943 : NodeCoverage93 [31,31,16] 16 15 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0944 : NodeCoverage93 [31,31,15] 15 16 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0945 : NodeCoverage93 [31,31,14] 14 17 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0946 : NodeCoverage93 [31,31,13] 13 18 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0947 : NodeCoverage93 [31,31,12] 12 19 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0948 : NodeCoverage93 [31,31,11] 11 20 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0949 : NodeCoverage93 [31,31,10] 10 21 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0950 : NodeCoverage93 [31,31,9] 9 22 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0951 : NodeCoverage93 [31,31,8] 8 23 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0952 : NodeCoverage93 [31,31,7] 7 24 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0953 : NodeCoverage93 [31,31,6] 6 25 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0954 : NodeCoverage93 [31,31,5] 5 26 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0955 : NodeCoverage93 [31,31,3] 3 28 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0956 : NodeCoverage93 [31,31] 31 31 :=
  node_fork93 (B := [31,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3]) (by decide +kernel) (by decide +kernel)
    (ChildrenCoverage93.cons _ _ compact93_node_0930
    (ChildrenCoverage93.cons _ _ compact93_node_0931
    (ChildrenCoverage93.cons _ _ compact93_node_0932
    (ChildrenCoverage93.cons _ _ compact93_node_0933
    (ChildrenCoverage93.cons _ _ compact93_node_0934
    (ChildrenCoverage93.cons _ _ compact93_node_0935
    (ChildrenCoverage93.cons _ _ compact93_node_0936
    (ChildrenCoverage93.cons _ _ compact93_node_0937
    (ChildrenCoverage93.cons _ _ compact93_node_0938
    (ChildrenCoverage93.cons _ _ compact93_node_0939
    (ChildrenCoverage93.cons _ _ compact93_node_0940
    (ChildrenCoverage93.cons _ _ compact93_node_0941
    (ChildrenCoverage93.cons _ _ compact93_node_0942
    (ChildrenCoverage93.cons _ _ compact93_node_0943
    (ChildrenCoverage93.cons _ _ compact93_node_0944
    (ChildrenCoverage93.cons _ _ compact93_node_0945
    (ChildrenCoverage93.cons _ _ compact93_node_0946
    (ChildrenCoverage93.cons _ _ compact93_node_0947
    (ChildrenCoverage93.cons _ _ compact93_node_0948
    (ChildrenCoverage93.cons _ _ compact93_node_0949
    (ChildrenCoverage93.cons _ _ compact93_node_0950
    (ChildrenCoverage93.cons _ _ compact93_node_0951
    (ChildrenCoverage93.cons _ _ compact93_node_0952
    (ChildrenCoverage93.cons _ _ compact93_node_0953
    (ChildrenCoverage93.cons _ _ compact93_node_0954
    (ChildrenCoverage93.cons _ _ compact93_node_0955
    ChildrenCoverage93.nil))))))))))))))))))))))))))

theorem compact93_node_0957 : NodeCoverage93 [31,30] 30 32 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0958 : NodeCoverage93 [31,29] 29 33 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0959 : NodeCoverage93 [31,28] 28 34 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0960 : NodeCoverage93 [31,27] 27 35 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0961 : NodeCoverage93 [31,26] 26 36 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0962 : NodeCoverage93 [31,25] 25 37 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0963 : NodeCoverage93 [31,24] 24 38 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0964 : NodeCoverage93 [31,23] 23 39 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0965 : NodeCoverage93 [31,22] 22 40 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0966 : NodeCoverage93 [31,21] 21 41 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0967 : NodeCoverage93 [31,20] 20 42 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0968 : NodeCoverage93 [31,19] 19 43 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0969 : NodeCoverage93 [31,18] 18 44 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0970 : NodeCoverage93 [31,17] 17 45 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0971 : NodeCoverage93 [31,16] 16 46 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0972 : NodeCoverage93 [31,15] 15 47 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0973 : NodeCoverage93 [31,14] 14 48 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0974 : NodeCoverage93 [31,13] 13 49 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0975 : NodeCoverage93 [31,12] 12 50 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem compact93_node_0976 : NodeCoverage93 [31,11] 11 51 :=
  demand_node_prune93 31 compact93_demands_31 compact93_demands_31_exact
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Symconf93
