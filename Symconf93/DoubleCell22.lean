module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w22_23 : List LocalWitness31 := []
private theorem c22_23 : CellCovers31 22 23 := by
  have H : (w22_23.all (validWitness31 proto5) && doubleCoverage31 w22_23 22 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_24 : List LocalWitness31 := []
private theorem c22_24 : CellCovers31 22 24 := by
  have H : (w22_24.all (validWitness31 proto5) && doubleCoverage31 w22_24 22 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_25 : List LocalWitness31 := []
private theorem c22_25 : CellCovers31 22 25 := by
  have H : (w22_25.all (validWitness31 proto5) && doubleCoverage31 w22_25 22 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_26 : List LocalWitness31 := []
private theorem c22_26 : CellCovers31 22 26 := by
  have H : (w22_26.all (validWitness31 proto5) && doubleCoverage31 w22_26 22 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_27 : List LocalWitness31 := []
private theorem c22_27 : CellCovers31 22 27 := by
  have H : (w22_27.all (validWitness31 proto5) && doubleCoverage31 w22_27 22 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_28 : List LocalWitness31 := []
private theorem c22_28 : CellCovers31 22 28 := by
  have H : (w22_28.all (validWitness31 proto5) && doubleCoverage31 w22_28 22 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_29 : List LocalWitness31 := []
private theorem c22_29 : CellCovers31 22 29 := by
  have H : (w22_29.all (validWitness31 proto5) && doubleCoverage31 w22_29 22 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w22_30 : List LocalWitness31 := []
private theorem c22_30 : CellCovers31 22 30 := by
  have H : (w22_30.all (validWitness31 proto5) && doubleCoverage31 w22_30 22 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row22 (v : Fin 31) (h : 22<v.val) : CellCovers31 22 v.val := by
  fin_cases v
  · change 22<0 at h; omega
  · change 22<1 at h; omega
  · change 22<2 at h; omega
  · change 22<3 at h; omega
  · change 22<4 at h; omega
  · change 22<5 at h; omega
  · change 22<6 at h; omega
  · change 22<7 at h; omega
  · change 22<8 at h; omega
  · change 22<9 at h; omega
  · change 22<10 at h; omega
  · change 22<11 at h; omega
  · change 22<12 at h; omega
  · change 22<13 at h; omega
  · change 22<14 at h; omega
  · change 22<15 at h; omega
  · change 22<16 at h; omega
  · change 22<17 at h; omega
  · change 22<18 at h; omega
  · change 22<19 at h; omega
  · change 22<20 at h; omega
  · change 22<21 at h; omega
  · change 22<22 at h; omega
  · exact c22_23
  · exact c22_24
  · exact c22_25
  · exact c22_26
  · exact c22_27
  · exact c22_28
  · exact c22_29
  · exact c22_30

end Symconf93
