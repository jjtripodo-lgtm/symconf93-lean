module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w08_09 : List LocalWitness31 := []
private theorem c08_09 : CellCovers31 8 9 := by
  have H : (w08_09.all (validWitness31 proto5) && doubleCoverage31 w08_09 8 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_10 : List LocalWitness31 := [⟨140545,6,false,8⟩,⟨533761,1,false,8⟩,⟨541953,5,false,8⟩,⟨558337,23,false,8⟩,⟨16786689,71,false,8⟩,⟨17302785,62,true,10⟩,⟨33563905,74,false,8⟩,⟨67126529,75,false,8⟩,⟨67634433,46,true,10⟩,⟨71304449,79,true,10⟩,⟨272631041,18,true,10⟩,⟨285213953,70,true,10⟩]
private theorem c08_10 : CellCovers31 8 10 := by
  have H : (w08_10.all (validWitness31 proto5) && doubleCoverage31 w08_10 8 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_11 : List LocalWitness31 := [⟨141569,7,true,13⟩,⟨166145,48,true,17⟩,⟨134228225,82,true,13⟩,⟨134351105,61,false,8⟩,⟨134482177,45,false,8⟩,⟨536905985,70,false,29⟩,⟨537004289,18,false,29⟩]
private theorem c08_11 : CellCovers31 8 11 := by
  have H : (w08_11.all (validWitness31 proto5) && doubleCoverage31 w08_11 8 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_12 : List LocalWitness31 := [⟨168193,50,true,17⟩,⟨2117889,11,true,14⟩,⟨2134273,36,true,15⟩,⟨33591553,76,true,15⟩,⟨67145985,83,true,15⟩,⟨270536961,45,true,0⟩,⟨272634113,61,true,0⟩,⟨335548673,82,false,26⟩]
private theorem c08_12 : CellCovers31 8 12 := by
  have H : (w08_12.all (validWitness31 proto5) && doubleCoverage31 w08_12 8 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_13 : List LocalWitness31 := [⟨565505,37,false,13⟩,⟨663809,13,true,19⟩,⟨1188097,14,true,20⟩,⟨33595649,77,true,15⟩,⟨151003393,83,false,24⟩,⟨537010433,79,false,29⟩,⟨537927937,46,false,29⟩,⟨570433793,75,true,0⟩]
private theorem c08_13 : CellCovers31 8 13 := by
  have H : (w08_13.all (validWitness31 proto5) && doubleCoverage31 w08_13 8 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_14 : List LocalWitness31 := [⟨2638081,15,true,21⟩,⟨83902721,77,false,24⟩,⟨151011585,76,false,24⟩,⟨603996417,74,true,0⟩]
private theorem c08_14 : CellCovers31 8 14 := by
  have H : (w08_14.all (validWitness31 proto5) && doubleCoverage31 w08_14 8 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_15 : List LocalWitness31 := [⟨1212673,55,false,15⟩,⟨1343745,42,true,20⟩,⟨2261249,63,false,15⟩,⟨2654465,43,true,21⟩,⟨537952513,62,false,29⟩,⟨604012801,71,true,0⟩]
private theorem c08_15 : CellCovers31 8 15 := by
  have H : (w08_15.all (validWitness31 proto5) && doubleCoverage31 w08_15 8 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_16 : List LocalWitness31 := []
private theorem c08_16 : CellCovers31 8 16 := by
  have H : (w08_16.all (validWitness31 proto5) && doubleCoverage31 w08_16 8 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_17 : List LocalWitness31 := []
private theorem c08_17 : CellCovers31 8 17 := by
  have H : (w08_17.all (validWitness31 proto5) && doubleCoverage31 w08_17 8 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_18 : List LocalWitness31 := [⟨18088193,43,false,18⟩,⟨21233921,63,true,24⟩,⟨34865409,15,false,18⟩,⟨151257345,36,false,24⟩,⟨168034561,11,false,25⟩]
private theorem c08_18 : CellCovers31 8 18 := by
  have H : (w08_18.all (validWitness31 proto5) && doubleCoverage31 w08_18 8 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_19 : List LocalWitness31 := [⟨19398913,42,false,19⟩,⟨21496065,55,true,24⟩,⟨71827713,14,false,19⟩]
private theorem c08_19 : CellCovers31 8 19 := by
  have H : (w08_19.all (validWitness31 proto5) && doubleCoverage31 w08_19 8 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_20 : List LocalWitness31 := [⟨72352001,13,false,20⟩,⟨84934913,37,true,26⟩,⟨554696961,23,true,0⟩,⟨571474177,5,true,0⟩,⟨605028609,1,true,0⟩]
private theorem c08_20 : CellCovers31 8 20 := by
  have H : (w08_20.all (validWitness31 proto5) && doubleCoverage31 w08_20 8 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_21 : List LocalWitness31 := []
private theorem c08_21 : CellCovers31 8 21 := by
  have H : (w08_21.all (validWitness31 proto5) && doubleCoverage31 w08_21 8 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_22 : List LocalWitness31 := [⟨155189505,50,false,22⟩,⟨289407233,48,false,22⟩,⟨339738881,7,false,26⟩,⟨608174337,6,true,0⟩]
private theorem c08_22 : CellCovers31 8 22 := by
  have H : (w08_22.all (validWitness31 proto5) && doubleCoverage31 w08_22 8 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_23 : List LocalWitness31 := []
private theorem c08_23 : CellCovers31 8 23 := by
  have H : (w08_23.all (validWitness31 proto5) && doubleCoverage31 w08_23 8 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_24 : List LocalWitness31 := []
private theorem c08_24 : CellCovers31 8 24 := by
  have H : (w08_24.all (validWitness31 proto5) && doubleCoverage31 w08_24 8 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_25 : List LocalWitness31 := []
private theorem c08_25 : CellCovers31 8 25 := by
  have H : (w08_25.all (validWitness31 proto5) && doubleCoverage31 w08_25 8 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_26 : List LocalWitness31 := []
private theorem c08_26 : CellCovers31 8 26 := by
  have H : (w08_26.all (validWitness31 proto5) && doubleCoverage31 w08_26 8 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_27 : List LocalWitness31 := []
private theorem c08_27 : CellCovers31 8 27 := by
  have H : (w08_27.all (validWitness31 proto5) && doubleCoverage31 w08_27 8 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_28 : List LocalWitness31 := []
private theorem c08_28 : CellCovers31 8 28 := by
  have H : (w08_28.all (validWitness31 proto5) && doubleCoverage31 w08_28 8 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_29 : List LocalWitness31 := []
private theorem c08_29 : CellCovers31 8 29 := by
  have H : (w08_29.all (validWitness31 proto5) && doubleCoverage31 w08_29 8 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w08_30 : List LocalWitness31 := []
private theorem c08_30 : CellCovers31 8 30 := by
  have H : (w08_30.all (validWitness31 proto5) && doubleCoverage31 w08_30 8 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row08 (v : Fin 31) (h : 8<v.val) : CellCovers31 8 v.val := by
  fin_cases v
  · change 8<0 at h; omega
  · change 8<1 at h; omega
  · change 8<2 at h; omega
  · change 8<3 at h; omega
  · change 8<4 at h; omega
  · change 8<5 at h; omega
  · change 8<6 at h; omega
  · change 8<7 at h; omega
  · change 8<8 at h; omega
  · exact c08_09
  · exact c08_10
  · exact c08_11
  · exact c08_12
  · exact c08_13
  · exact c08_14
  · exact c08_15
  · exact c08_16
  · exact c08_17
  · exact c08_18
  · exact c08_19
  · exact c08_20
  · exact c08_21
  · exact c08_22
  · exact c08_23
  · exact c08_24
  · exact c08_25
  · exact c08_26
  · exact c08_27
  · exact c08_28
  · exact c08_29
  · exact c08_30

end Symconf93
