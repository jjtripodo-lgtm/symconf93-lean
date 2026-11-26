module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w24_25 : List LocalWitness31 := []
private theorem c24_25 : CellCovers31 24 25 := by
  have H : (w24_25.all (validWitness31 proto5) && doubleCoverage31 w24_25 24 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w24_26 : List LocalWitness31 := []
private theorem c24_26 : CellCovers31 24 26 := by
  have H : (w24_26.all (validWitness31 proto5) && doubleCoverage31 w24_26 24 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w24_27 : List LocalWitness31 := []
private theorem c24_27 : CellCovers31 24 27 := by
  have H : (w24_27.all (validWitness31 proto5) && doubleCoverage31 w24_27 24 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w24_28 : List LocalWitness31 := []
private theorem c24_28 : CellCovers31 24 28 := by
  have H : (w24_28.all (validWitness31 proto5) && doubleCoverage31 w24_28 24 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w24_29 : List LocalWitness31 := []
private theorem c24_29 : CellCovers31 24 29 := by
  have H : (w24_29.all (validWitness31 proto5) && doubleCoverage31 w24_29 24 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w24_30 : List LocalWitness31 := []
private theorem c24_30 : CellCovers31 24 30 := by
  have H : (w24_30.all (validWitness31 proto5) && doubleCoverage31 w24_30 24 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row24 (v : Fin 31) (h : 24<v.val) : CellCovers31 24 v.val := by
  fin_cases v
  · change 24<0 at h; omega
  · change 24<1 at h; omega
  · change 24<2 at h; omega
  · change 24<3 at h; omega
  · change 24<4 at h; omega
  · change 24<5 at h; omega
  · change 24<6 at h; omega
  · change 24<7 at h; omega
  · change 24<8 at h; omega
  · change 24<9 at h; omega
  · change 24<10 at h; omega
  · change 24<11 at h; omega
  · change 24<12 at h; omega
  · change 24<13 at h; omega
  · change 24<14 at h; omega
  · change 24<15 at h; omega
  · change 24<16 at h; omega
  · change 24<17 at h; omega
  · change 24<18 at h; omega
  · change 24<19 at h; omega
  · change 24<20 at h; omega
  · change 24<21 at h; omega
  · change 24<22 at h; omega
  · change 24<23 at h; omega
  · change 24<24 at h; omega
  · exact c24_25
  · exact c24_26
  · exact c24_27
  · exact c24_28
  · exact c24_29
  · exact c24_30

end Symconf93
