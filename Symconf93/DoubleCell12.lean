module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w12_13 : List LocalWitness31 := []
private theorem c12_13 : CellCovers31 12 13 := by
  have H : (w12_13.all (validWitness31 proto5) && doubleCoverage31 w12_13 12 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_14 : List LocalWitness31 := [⟨2379777,10,false,12⟩,⟨8671233,13,false,12⟩,⟨35672065,16,false,12⟩,⟨37769217,18,false,12⟩,⟨135286785,84,false,12⟩,⟨136335361,78,false,12⟩,⟨138432513,79,false,12⟩]
private theorem c12_14 : CellCovers31 12 14 := by
  have H : (w12_14.all (validWitness31 proto5) && doubleCoverage31 w12_14 12 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_15 : List LocalWitness31 := [⟨2265089,51,true,17⟩,⟨5279745,22,true,22⟩,⟨33722369,74,true,17⟩,⟨71340033,59,false,12⟩]
private theorem c12_15 : CellCovers31 12 15 := by
  have H : (w12_15.all (validWitness31 proto5) && doubleCoverage31 w12_15 12 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_16 : List LocalWitness31 := [⟨2428929,31,false,16⟩,⟨8720385,37,true,18⟩,⟨10555393,23,true,23⟩,⟨42012673,41,false,23⟩,⟨67440641,75,true,18⟩,⟨75567105,58,false,23⟩,⟨539037697,79,true,0⟩,⟨541134849,78,true,0⟩,⟨545329153,84,true,0⟩]
private theorem c12_16 : CellCovers31 12 16 := by
  have H : (w12_16.all (validWitness31 proto5) && doubleCoverage31 w12_16 12 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_17 : List LocalWitness31 := [⟨10620929,5,true,23⟩,⟨135401473,58,true,20⟩,⟨167907329,75,false,25⟩,⟨270667777,59,true,0⟩]
private theorem c12_17 : CellCovers31 12 17 := by
  have H : (w12_17.all (validWitness31 proto5) && doubleCoverage31 w12_17 12 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_18 : List LocalWitness31 := [⟨10752001,1,true,23⟩,⟨135532545,41,true,20⟩,⟨335810561,74,false,26⟩,⟨539234305,18,true,0⟩,⟨541331457,16,true,0⟩]
private theorem c12_18 : CellCovers31 12 18 := by
  have H : (w12_18.all (validWitness31 proto5) && doubleCoverage31 w12_18 12 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_19 : List LocalWitness31 := []
private theorem c12_19 : CellCovers31 12 19 := by
  have H : (w12_19.all (validWitness31 proto5) && doubleCoverage31 w12_19 12 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_20 : List LocalWitness31 := [⟨38801409,1,false,20⟩,⟨72355841,5,false,20⟩,⟨139464705,23,false,20⟩,⟨168824833,37,false,25⟩,⟨571478017,13,true,0⟩]
private theorem c12_20 : CellCovers31 12 20 := by
  have H : (w12_20.all (validWitness31 proto5) && doubleCoverage31 w12_20 12 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_21 : List LocalWitness31 := [⟨278925313,22,false,21⟩]
private theorem c12_21 : CellCovers31 12 21 := by
  have H : (w12_21.all (validWitness31 proto5) && doubleCoverage31 w12_21 12 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_22 : List LocalWitness31 := [⟨171970561,31,true,27⟩,⟨339742721,51,false,26⟩,⟨574623745,10,true,0⟩]
private theorem c12_22 : CellCovers31 12 22 := by
  have H : (w12_22.all (validWitness31 proto5) && doubleCoverage31 w12_22 12 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_23 : List LocalWitness31 := []
private theorem c12_23 : CellCovers31 12 23 := by
  have H : (w12_23.all (validWitness31 proto5) && doubleCoverage31 w12_23 12 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_24 : List LocalWitness31 := []
private theorem c12_24 : CellCovers31 12 24 := by
  have H : (w12_24.all (validWitness31 proto5) && doubleCoverage31 w12_24 12 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_25 : List LocalWitness31 := []
private theorem c12_25 : CellCovers31 12 25 := by
  have H : (w12_25.all (validWitness31 proto5) && doubleCoverage31 w12_25 12 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_26 : List LocalWitness31 := []
private theorem c12_26 : CellCovers31 12 26 := by
  have H : (w12_26.all (validWitness31 proto5) && doubleCoverage31 w12_26 12 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_27 : List LocalWitness31 := []
private theorem c12_27 : CellCovers31 12 27 := by
  have H : (w12_27.all (validWitness31 proto5) && doubleCoverage31 w12_27 12 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_28 : List LocalWitness31 := []
private theorem c12_28 : CellCovers31 12 28 := by
  have H : (w12_28.all (validWitness31 proto5) && doubleCoverage31 w12_28 12 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_29 : List LocalWitness31 := []
private theorem c12_29 : CellCovers31 12 29 := by
  have H : (w12_29.all (validWitness31 proto5) && doubleCoverage31 w12_29 12 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w12_30 : List LocalWitness31 := []
private theorem c12_30 : CellCovers31 12 30 := by
  have H : (w12_30.all (validWitness31 proto5) && doubleCoverage31 w12_30 12 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row12 (v : Fin 31) (h : 12<v.val) : CellCovers31 12 v.val := by
  fin_cases v
  · change 12<0 at h; omega
  · change 12<1 at h; omega
  · change 12<2 at h; omega
  · change 12<3 at h; omega
  · change 12<4 at h; omega
  · change 12<5 at h; omega
  · change 12<6 at h; omega
  · change 12<7 at h; omega
  · change 12<8 at h; omega
  · change 12<9 at h; omega
  · change 12<10 at h; omega
  · change 12<11 at h; omega
  · change 12<12 at h; omega
  · exact c12_13
  · exact c12_14
  · exact c12_15
  · exact c12_16
  · exact c12_17
  · exact c12_18
  · exact c12_19
  · exact c12_20
  · exact c12_21
  · exact c12_22
  · exact c12_23
  · exact c12_24
  · exact c12_25
  · exact c12_26
  · exact c12_27
  · exact c12_28
  · exact c12_29
  · exact c12_30

end Symconf93
