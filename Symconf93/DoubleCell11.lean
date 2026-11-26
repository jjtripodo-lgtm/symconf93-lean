module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w11_12 : List LocalWitness31 := []
private theorem c11_12 : CellCovers31 11 12 := by
  have H : (w11_12.all (validWitness31 proto5) && doubleCoverage31 w11_12 11 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_13 : List LocalWitness31 := [⟨8464385,42,false,11⟩,⟨33630209,86,false,11⟩,⟨268969985,88,false,11⟩,⟨276834305,90,false,11⟩]
private theorem c11_13 : CellCovers31 11 13 := by
  have H : (w11_13.all (validWitness31 proto5) && doubleCoverage31 w11_13 11 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_14 : List LocalWitness31 := [⟨8472577,55,true,16⟩,⟨8669185,14,false,11⟩,⟨16861185,71,true,16⟩,⟨67389441,83,false,11⟩,⟨83904513,89,false,24⟩,⟨537413633,90,true,0⟩,⟨545277953,88,true,0⟩]
private theorem c11_14 : CellCovers31 11 14 := by
  have H : (w11_14.all (validWitness31 proto5) && doubleCoverage31 w11_14 11 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_15 : List LocalWitness31 := []
private theorem c11_15 : CellCovers31 11 15 := by
  have H : (w11_15.all (validWitness31 proto5) && doubleCoverage31 w11_15 11 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_16 : List LocalWitness31 := [⟨42010625,56,false,23⟩,⟨268765185,89,true,18⟩,⟨285280257,83,true,0⟩]
private theorem c11_16 : CellCovers31 11 16 := by
  have H : (w11_16.all (validWitness31 proto5) && doubleCoverage31 w11_16 11 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_17 : List LocalWitness31 := [⟨67766273,56,true,19⟩,⟨604112897,86,true,0⟩]
private theorem c11_17 : CellCovers31 11 17 := by
  have H : (w11_17.all (validWitness31 proto5) && doubleCoverage31 w11_17 11 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_18 : List LocalWitness31 := [⟨335808513,71,false,26⟩]
private theorem c11_18 : CellCovers31 11 18 := by
  have H : (w11_18.all (validWitness31 proto5) && doubleCoverage31 w11_18 11 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_19 : List LocalWitness31 := [⟨285739009,14,true,0⟩,⟨336070657,55,false,26⟩,⟨604506113,42,true,0⟩]
private theorem c11_19 : CellCovers31 11 19 := by
  have H : (w11_19.all (validWitness31 proto5) && doubleCoverage31 w11_19 11 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_20 : List LocalWitness31 := []
private theorem c11_20 : CellCovers31 11 20 := by
  have H : (w11_20.all (validWitness31 proto5) && doubleCoverage31 w11_20 11 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_21 : List LocalWitness31 := []
private theorem c11_21 : CellCovers31 11 21 := by
  have H : (w11_21.all (validWitness31 proto5) && doubleCoverage31 w11_21 11 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_22 : List LocalWitness31 := []
private theorem c11_22 : CellCovers31 11 22 := by
  have H : (w11_22.all (validWitness31 proto5) && doubleCoverage31 w11_22 11 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_23 : List LocalWitness31 := []
private theorem c11_23 : CellCovers31 11 23 := by
  have H : (w11_23.all (validWitness31 proto5) && doubleCoverage31 w11_23 11 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_24 : List LocalWitness31 := []
private theorem c11_24 : CellCovers31 11 24 := by
  have H : (w11_24.all (validWitness31 proto5) && doubleCoverage31 w11_24 11 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_25 : List LocalWitness31 := []
private theorem c11_25 : CellCovers31 11 25 := by
  have H : (w11_25.all (validWitness31 proto5) && doubleCoverage31 w11_25 11 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_26 : List LocalWitness31 := []
private theorem c11_26 : CellCovers31 11 26 := by
  have H : (w11_26.all (validWitness31 proto5) && doubleCoverage31 w11_26 11 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_27 : List LocalWitness31 := []
private theorem c11_27 : CellCovers31 11 27 := by
  have H : (w11_27.all (validWitness31 proto5) && doubleCoverage31 w11_27 11 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_28 : List LocalWitness31 := []
private theorem c11_28 : CellCovers31 11 28 := by
  have H : (w11_28.all (validWitness31 proto5) && doubleCoverage31 w11_28 11 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_29 : List LocalWitness31 := []
private theorem c11_29 : CellCovers31 11 29 := by
  have H : (w11_29.all (validWitness31 proto5) && doubleCoverage31 w11_29 11 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w11_30 : List LocalWitness31 := []
private theorem c11_30 : CellCovers31 11 30 := by
  have H : (w11_30.all (validWitness31 proto5) && doubleCoverage31 w11_30 11 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row11 (v : Fin 31) (h : 11<v.val) : CellCovers31 11 v.val := by
  fin_cases v
  · change 11<0 at h; omega
  · change 11<1 at h; omega
  · change 11<2 at h; omega
  · change 11<3 at h; omega
  · change 11<4 at h; omega
  · change 11<5 at h; omega
  · change 11<6 at h; omega
  · change 11<7 at h; omega
  · change 11<8 at h; omega
  · change 11<9 at h; omega
  · change 11<10 at h; omega
  · change 11<11 at h; omega
  · exact c11_12
  · exact c11_13
  · exact c11_14
  · exact c11_15
  · exact c11_16
  · exact c11_17
  · exact c11_18
  · exact c11_19
  · exact c11_20
  · exact c11_21
  · exact c11_22
  · exact c11_23
  · exact c11_24
  · exact c11_25
  · exact c11_26
  · exact c11_27
  · exact c11_28
  · exact c11_29
  · exact c11_30

end Symconf93
