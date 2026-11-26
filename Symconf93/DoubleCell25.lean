module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w25_26 : List LocalWitness31 := []
private theorem c25_26 : CellCovers31 25 26 := by
  have H : (w25_26.all (validWitness31 proto5) && doubleCoverage31 w25_26 25 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w25_27 : List LocalWitness31 := []
private theorem c25_27 : CellCovers31 25 27 := by
  have H : (w25_27.all (validWitness31 proto5) && doubleCoverage31 w25_27 25 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w25_28 : List LocalWitness31 := []
private theorem c25_28 : CellCovers31 25 28 := by
  have H : (w25_28.all (validWitness31 proto5) && doubleCoverage31 w25_28 25 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w25_29 : List LocalWitness31 := []
private theorem c25_29 : CellCovers31 25 29 := by
  have H : (w25_29.all (validWitness31 proto5) && doubleCoverage31 w25_29 25 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w25_30 : List LocalWitness31 := []
private theorem c25_30 : CellCovers31 25 30 := by
  have H : (w25_30.all (validWitness31 proto5) && doubleCoverage31 w25_30 25 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row25 (v : Fin 31) (h : 25<v.val) : CellCovers31 25 v.val := by
  fin_cases v
  · change 25<0 at h; omega
  · change 25<1 at h; omega
  · change 25<2 at h; omega
  · change 25<3 at h; omega
  · change 25<4 at h; omega
  · change 25<5 at h; omega
  · change 25<6 at h; omega
  · change 25<7 at h; omega
  · change 25<8 at h; omega
  · change 25<9 at h; omega
  · change 25<10 at h; omega
  · change 25<11 at h; omega
  · change 25<12 at h; omega
  · change 25<13 at h; omega
  · change 25<14 at h; omega
  · change 25<15 at h; omega
  · change 25<16 at h; omega
  · change 25<17 at h; omega
  · change 25<18 at h; omega
  · change 25<19 at h; omega
  · change 25<20 at h; omega
  · change 25<21 at h; omega
  · change 25<22 at h; omega
  · change 25<23 at h; omega
  · change 25<24 at h; omega
  · change 25<25 at h; omega
  · exact c25_26
  · exact c25_27
  · exact c25_28
  · exact c25_29
  · exact c25_30

end Symconf93
