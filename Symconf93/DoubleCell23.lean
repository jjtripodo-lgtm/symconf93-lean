module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w23_24 : List LocalWitness31 := []
private theorem c23_24 : CellCovers31 23 24 := by
  have H : (w23_24.all (validWitness31 proto5) && doubleCoverage31 w23_24 23 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w23_25 : List LocalWitness31 := []
private theorem c23_25 : CellCovers31 23 25 := by
  have H : (w23_25.all (validWitness31 proto5) && doubleCoverage31 w23_25 23 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w23_26 : List LocalWitness31 := []
private theorem c23_26 : CellCovers31 23 26 := by
  have H : (w23_26.all (validWitness31 proto5) && doubleCoverage31 w23_26 23 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w23_27 : List LocalWitness31 := []
private theorem c23_27 : CellCovers31 23 27 := by
  have H : (w23_27.all (validWitness31 proto5) && doubleCoverage31 w23_27 23 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w23_28 : List LocalWitness31 := []
private theorem c23_28 : CellCovers31 23 28 := by
  have H : (w23_28.all (validWitness31 proto5) && doubleCoverage31 w23_28 23 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w23_29 : List LocalWitness31 := []
private theorem c23_29 : CellCovers31 23 29 := by
  have H : (w23_29.all (validWitness31 proto5) && doubleCoverage31 w23_29 23 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w23_30 : List LocalWitness31 := []
private theorem c23_30 : CellCovers31 23 30 := by
  have H : (w23_30.all (validWitness31 proto5) && doubleCoverage31 w23_30 23 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row23 (v : Fin 31) (h : 23<v.val) : CellCovers31 23 v.val := by
  fin_cases v
  · change 23<0 at h; omega
  · change 23<1 at h; omega
  · change 23<2 at h; omega
  · change 23<3 at h; omega
  · change 23<4 at h; omega
  · change 23<5 at h; omega
  · change 23<6 at h; omega
  · change 23<7 at h; omega
  · change 23<8 at h; omega
  · change 23<9 at h; omega
  · change 23<10 at h; omega
  · change 23<11 at h; omega
  · change 23<12 at h; omega
  · change 23<13 at h; omega
  · change 23<14 at h; omega
  · change 23<15 at h; omega
  · change 23<16 at h; omega
  · change 23<17 at h; omega
  · change 23<18 at h; omega
  · change 23<19 at h; omega
  · change 23<20 at h; omega
  · change 23<21 at h; omega
  · change 23<22 at h; omega
  · change 23<23 at h; omega
  · exact c23_24
  · exact c23_25
  · exact c23_26
  · exact c23_27
  · exact c23_28
  · exact c23_29
  · exact c23_30

end Symconf93
