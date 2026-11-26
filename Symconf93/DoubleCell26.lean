module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w26_27 : List LocalWitness31 := []
private theorem c26_27 : CellCovers31 26 27 := by
  have H : (w26_27.all (validWitness31 proto5) && doubleCoverage31 w26_27 26 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w26_28 : List LocalWitness31 := []
private theorem c26_28 : CellCovers31 26 28 := by
  have H : (w26_28.all (validWitness31 proto5) && doubleCoverage31 w26_28 26 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w26_29 : List LocalWitness31 := []
private theorem c26_29 : CellCovers31 26 29 := by
  have H : (w26_29.all (validWitness31 proto5) && doubleCoverage31 w26_29 26 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w26_30 : List LocalWitness31 := []
private theorem c26_30 : CellCovers31 26 30 := by
  have H : (w26_30.all (validWitness31 proto5) && doubleCoverage31 w26_30 26 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row26 (v : Fin 31) (h : 26<v.val) : CellCovers31 26 v.val := by
  fin_cases v
  · change 26<0 at h; omega
  · change 26<1 at h; omega
  · change 26<2 at h; omega
  · change 26<3 at h; omega
  · change 26<4 at h; omega
  · change 26<5 at h; omega
  · change 26<6 at h; omega
  · change 26<7 at h; omega
  · change 26<8 at h; omega
  · change 26<9 at h; omega
  · change 26<10 at h; omega
  · change 26<11 at h; omega
  · change 26<12 at h; omega
  · change 26<13 at h; omega
  · change 26<14 at h; omega
  · change 26<15 at h; omega
  · change 26<16 at h; omega
  · change 26<17 at h; omega
  · change 26<18 at h; omega
  · change 26<19 at h; omega
  · change 26<20 at h; omega
  · change 26<21 at h; omega
  · change 26<22 at h; omega
  · change 26<23 at h; omega
  · change 26<24 at h; omega
  · change 26<25 at h; omega
  · change 26<26 at h; omega
  · exact c26_27
  · exact c26_28
  · exact c26_29
  · exact c26_30

end Symconf93
