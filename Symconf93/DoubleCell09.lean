module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w09_10 : List LocalWitness31 := []
private theorem c09_10 : CellCovers31 9 10 := by
  have H : (w09_10.all (validWitness31 proto5) && doubleCoverage31 w09_10 9 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_11 : List LocalWitness31 := [⟨592385,22,false,9⟩,⟨16796161,72,false,9⟩,⟨17304065,46,false,9⟩,⟨67635713,62,false,9⟩,⟨134351361,73,false,9⟩,⟨268470785,85,false,9⟩,⟨285215233,87,true,11⟩]
private theorem c09_11 : CellCovers31 9 11 := by
  have H : (w09_11.all (validWitness31 proto5) && doubleCoverage31 w09_11 9 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_12 : List LocalWitness31 := [⟨33575425,86,true,14⟩,⟨41947649,88,false,23⟩,⟨134353409,80,false,9⟩,⟨536941057,87,false,29⟩,⟨570429953,85,true,0⟩]
private theorem c09_12 : CellCovers31 9 12 := by
  have H : (w09_12.all (validWitness31 proto5) && doubleCoverage31 w09_12 9 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_13 : List LocalWitness31 := [⟨2171393,34,true,16⟩,⟨17310209,44,false,9⟩,⟨18883073,45,false,21⟩,⟨41951745,81,false,23⟩,⟨276832769,80,true,0⟩,⟨545268225,73,true,0⟩]
private theorem c09_13 : CellCovers31 9 13 := by
  have H : (w09_13.all (validWitness31 proto5) && doubleCoverage31 w09_13 9 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_14 : List LocalWitness31 := [⟨35668481,60,false,21⟩,⟨538984961,62,true,0⟩]
private theorem c09_14 : CellCovers31 9 14 := by
  have H : (w09_14.all (validWitness31 proto5) && doubleCoverage31 w09_14 9 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_15 : List LocalWitness31 := [⟨67666433,60,true,19⟩,⟨134382081,81,true,17⟩,⟨268599809,88,true,17⟩,⟨335577601,86,false,26⟩]
private theorem c09_15 : CellCovers31 9 15 := by
  have H : (w09_15.all (validWitness31 proto5) && doubleCoverage31 w09_15 9 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_16 : List LocalWitness31 := [⟨134808065,45,true,19⟩,⟨136380929,44,true,0⟩,⟨539034113,46,true,0⟩,⟨604045825,72,true,0⟩]
private theorem c09_16 : CellCovers31 9 16 := by
  have H : (w09_16.all (validWitness31 proto5) && doubleCoverage31 w09_16 9 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_17 : List LocalWitness31 := []
private theorem c09_17 : CellCovers31 9 17 := by
  have H : (w09_17.all (validWitness31 proto5) && doubleCoverage31 w09_17 9 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_18 : List LocalWitness31 := []
private theorem c09_18 : CellCovers31 9 18 := by
  have H : (w09_18.all (validWitness31 proto5) && doubleCoverage31 w09_18 9 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_19 : List LocalWitness31 := [⟨151519745,34,false,24⟩]
private theorem c09_19 : CellCovers31 9 19 := by
  have H : (w09_19.all (validWitness31 proto5) && doubleCoverage31 w09_19 9 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_20 : List LocalWitness31 := []
private theorem c09_20 : CellCovers31 9 20 := by
  have H : (w09_20.all (validWitness31 proto5) && doubleCoverage31 w09_20 9 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_21 : List LocalWitness31 := [⟨555745793,22,true,0⟩]
private theorem c09_21 : CellCovers31 9 21 := by
  have H : (w09_21.all (validWitness31 proto5) && doubleCoverage31 w09_21 9 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_22 : List LocalWitness31 := []
private theorem c09_22 : CellCovers31 9 22 := by
  have H : (w09_22.all (validWitness31 proto5) && doubleCoverage31 w09_22 9 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_23 : List LocalWitness31 := []
private theorem c09_23 : CellCovers31 9 23 := by
  have H : (w09_23.all (validWitness31 proto5) && doubleCoverage31 w09_23 9 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_24 : List LocalWitness31 := []
private theorem c09_24 : CellCovers31 9 24 := by
  have H : (w09_24.all (validWitness31 proto5) && doubleCoverage31 w09_24 9 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_25 : List LocalWitness31 := []
private theorem c09_25 : CellCovers31 9 25 := by
  have H : (w09_25.all (validWitness31 proto5) && doubleCoverage31 w09_25 9 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_26 : List LocalWitness31 := []
private theorem c09_26 : CellCovers31 9 26 := by
  have H : (w09_26.all (validWitness31 proto5) && doubleCoverage31 w09_26 9 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_27 : List LocalWitness31 := []
private theorem c09_27 : CellCovers31 9 27 := by
  have H : (w09_27.all (validWitness31 proto5) && doubleCoverage31 w09_27 9 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_28 : List LocalWitness31 := []
private theorem c09_28 : CellCovers31 9 28 := by
  have H : (w09_28.all (validWitness31 proto5) && doubleCoverage31 w09_28 9 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_29 : List LocalWitness31 := []
private theorem c09_29 : CellCovers31 9 29 := by
  have H : (w09_29.all (validWitness31 proto5) && doubleCoverage31 w09_29 9 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w09_30 : List LocalWitness31 := []
private theorem c09_30 : CellCovers31 9 30 := by
  have H : (w09_30.all (validWitness31 proto5) && doubleCoverage31 w09_30 9 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row09 (v : Fin 31) (h : 9<v.val) : CellCovers31 9 v.val := by
  fin_cases v
  · change 9<0 at h; omega
  · change 9<1 at h; omega
  · change 9<2 at h; omega
  · change 9<3 at h; omega
  · change 9<4 at h; omega
  · change 9<5 at h; omega
  · change 9<6 at h; omega
  · change 9<7 at h; omega
  · change 9<8 at h; omega
  · change 9<9 at h; omega
  · exact c09_10
  · exact c09_11
  · exact c09_12
  · exact c09_13
  · exact c09_14
  · exact c09_15
  · exact c09_16
  · exact c09_17
  · exact c09_18
  · exact c09_19
  · exact c09_20
  · exact c09_21
  · exact c09_22
  · exact c09_23
  · exact c09_24
  · exact c09_25
  · exact c09_26
  · exact c09_27
  · exact c09_28
  · exact c09_29
  · exact c09_30

end Symconf93
