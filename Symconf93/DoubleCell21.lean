module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w21_22 : List LocalWitness31 := []
private theorem c21_22 : CellCovers31 21 22 := by
  have H : (w21_22.all (validWitness31 proto5) && doubleCoverage31 w21_22 21 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_23 : List LocalWitness31 := []
private theorem c21_23 : CellCovers31 21 23 := by
  have H : (w21_23.all (validWitness31 proto5) && doubleCoverage31 w21_23 21 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_24 : List LocalWitness31 := []
private theorem c21_24 : CellCovers31 21 24 := by
  have H : (w21_24.all (validWitness31 proto5) && doubleCoverage31 w21_24 21 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_25 : List LocalWitness31 := []
private theorem c21_25 : CellCovers31 21 25 := by
  have H : (w21_25.all (validWitness31 proto5) && doubleCoverage31 w21_25 21 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_26 : List LocalWitness31 := []
private theorem c21_26 : CellCovers31 21 26 := by
  have H : (w21_26.all (validWitness31 proto5) && doubleCoverage31 w21_26 21 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_27 : List LocalWitness31 := []
private theorem c21_27 : CellCovers31 21 27 := by
  have H : (w21_27.all (validWitness31 proto5) && doubleCoverage31 w21_27 21 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_28 : List LocalWitness31 := []
private theorem c21_28 : CellCovers31 21 28 := by
  have H : (w21_28.all (validWitness31 proto5) && doubleCoverage31 w21_28 21 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_29 : List LocalWitness31 := []
private theorem c21_29 : CellCovers31 21 29 := by
  have H : (w21_29.all (validWitness31 proto5) && doubleCoverage31 w21_29 21 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w21_30 : List LocalWitness31 := []
private theorem c21_30 : CellCovers31 21 30 := by
  have H : (w21_30.all (validWitness31 proto5) && doubleCoverage31 w21_30 21 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row21 (v : Fin 31) (h : 21<v.val) : CellCovers31 21 v.val := by
  fin_cases v
  · change 21<0 at h; omega
  · change 21<1 at h; omega
  · change 21<2 at h; omega
  · change 21<3 at h; omega
  · change 21<4 at h; omega
  · change 21<5 at h; omega
  · change 21<6 at h; omega
  · change 21<7 at h; omega
  · change 21<8 at h; omega
  · change 21<9 at h; omega
  · change 21<10 at h; omega
  · change 21<11 at h; omega
  · change 21<12 at h; omega
  · change 21<13 at h; omega
  · change 21<14 at h; omega
  · change 21<15 at h; omega
  · change 21<16 at h; omega
  · change 21<17 at h; omega
  · change 21<18 at h; omega
  · change 21<19 at h; omega
  · change 21<20 at h; omega
  · change 21<21 at h; omega
  · exact c21_22
  · exact c21_23
  · exact c21_24
  · exact c21_25
  · exact c21_26
  · exact c21_27
  · exact c21_28
  · exact c21_29
  · exact c21_30

end Symconf93
