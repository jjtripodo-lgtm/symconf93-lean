module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w20_21 : List LocalWitness31 := []
private theorem c20_21 : CellCovers31 20 21 := by
  have H : (w20_21.all (validWitness31 proto5) && doubleCoverage31 w20_21 20 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_22 : List LocalWitness31 := []
private theorem c20_22 : CellCovers31 20 22 := by
  have H : (w20_22.all (validWitness31 proto5) && doubleCoverage31 w20_22 20 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_23 : List LocalWitness31 := []
private theorem c20_23 : CellCovers31 20 23 := by
  have H : (w20_23.all (validWitness31 proto5) && doubleCoverage31 w20_23 20 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_24 : List LocalWitness31 := []
private theorem c20_24 : CellCovers31 20 24 := by
  have H : (w20_24.all (validWitness31 proto5) && doubleCoverage31 w20_24 20 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_25 : List LocalWitness31 := []
private theorem c20_25 : CellCovers31 20 25 := by
  have H : (w20_25.all (validWitness31 proto5) && doubleCoverage31 w20_25 20 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_26 : List LocalWitness31 := []
private theorem c20_26 : CellCovers31 20 26 := by
  have H : (w20_26.all (validWitness31 proto5) && doubleCoverage31 w20_26 20 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_27 : List LocalWitness31 := []
private theorem c20_27 : CellCovers31 20 27 := by
  have H : (w20_27.all (validWitness31 proto5) && doubleCoverage31 w20_27 20 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_28 : List LocalWitness31 := []
private theorem c20_28 : CellCovers31 20 28 := by
  have H : (w20_28.all (validWitness31 proto5) && doubleCoverage31 w20_28 20 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_29 : List LocalWitness31 := []
private theorem c20_29 : CellCovers31 20 29 := by
  have H : (w20_29.all (validWitness31 proto5) && doubleCoverage31 w20_29 20 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w20_30 : List LocalWitness31 := []
private theorem c20_30 : CellCovers31 20 30 := by
  have H : (w20_30.all (validWitness31 proto5) && doubleCoverage31 w20_30 20 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row20 (v : Fin 31) (h : 20<v.val) : CellCovers31 20 v.val := by
  fin_cases v
  · change 20<0 at h; omega
  · change 20<1 at h; omega
  · change 20<2 at h; omega
  · change 20<3 at h; omega
  · change 20<4 at h; omega
  · change 20<5 at h; omega
  · change 20<6 at h; omega
  · change 20<7 at h; omega
  · change 20<8 at h; omega
  · change 20<9 at h; omega
  · change 20<10 at h; omega
  · change 20<11 at h; omega
  · change 20<12 at h; omega
  · change 20<13 at h; omega
  · change 20<14 at h; omega
  · change 20<15 at h; omega
  · change 20<16 at h; omega
  · change 20<17 at h; omega
  · change 20<18 at h; omega
  · change 20<19 at h; omega
  · change 20<20 at h; omega
  · exact c20_21
  · exact c20_22
  · exact c20_23
  · exact c20_24
  · exact c20_25
  · exact c20_26
  · exact c20_27
  · exact c20_28
  · exact c20_29
  · exact c20_30

end Symconf93
