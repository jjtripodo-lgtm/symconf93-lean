module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w28_29 : List LocalWitness31 := []
private theorem c28_29 : CellCovers31 28 29 := by
  have H : (w28_29.all (validWitness31 proto5) && doubleCoverage31 w28_29 28 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w28_30 : List LocalWitness31 := []
private theorem c28_30 : CellCovers31 28 30 := by
  have H : (w28_30.all (validWitness31 proto5) && doubleCoverage31 w28_30 28 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row28 (v : Fin 31) (h : 28<v.val) : CellCovers31 28 v.val := by
  fin_cases v
  · change 28<0 at h; omega
  · change 28<1 at h; omega
  · change 28<2 at h; omega
  · change 28<3 at h; omega
  · change 28<4 at h; omega
  · change 28<5 at h; omega
  · change 28<6 at h; omega
  · change 28<7 at h; omega
  · change 28<8 at h; omega
  · change 28<9 at h; omega
  · change 28<10 at h; omega
  · change 28<11 at h; omega
  · change 28<12 at h; omega
  · change 28<13 at h; omega
  · change 28<14 at h; omega
  · change 28<15 at h; omega
  · change 28<16 at h; omega
  · change 28<17 at h; omega
  · change 28<18 at h; omega
  · change 28<19 at h; omega
  · change 28<20 at h; omega
  · change 28<21 at h; omega
  · change 28<22 at h; omega
  · change 28<23 at h; omega
  · change 28<24 at h; omega
  · change 28<25 at h; omega
  · change 28<26 at h; omega
  · change 28<27 at h; omega
  · change 28<28 at h; omega
  · exact c28_29
  · exact c28_30

end Symconf93
