module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w27_28 : List LocalWitness31 := []
private theorem c27_28 : CellCovers31 27 28 := by
  have H : (w27_28.all (validWitness31 proto5) && doubleCoverage31 w27_28 27 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w27_29 : List LocalWitness31 := []
private theorem c27_29 : CellCovers31 27 29 := by
  have H : (w27_29.all (validWitness31 proto5) && doubleCoverage31 w27_29 27 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w27_30 : List LocalWitness31 := []
private theorem c27_30 : CellCovers31 27 30 := by
  have H : (w27_30.all (validWitness31 proto5) && doubleCoverage31 w27_30 27 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row27 (v : Fin 31) (h : 27<v.val) : CellCovers31 27 v.val := by
  fin_cases v
  · change 27<0 at h; omega
  · change 27<1 at h; omega
  · change 27<2 at h; omega
  · change 27<3 at h; omega
  · change 27<4 at h; omega
  · change 27<5 at h; omega
  · change 27<6 at h; omega
  · change 27<7 at h; omega
  · change 27<8 at h; omega
  · change 27<9 at h; omega
  · change 27<10 at h; omega
  · change 27<11 at h; omega
  · change 27<12 at h; omega
  · change 27<13 at h; omega
  · change 27<14 at h; omega
  · change 27<15 at h; omega
  · change 27<16 at h; omega
  · change 27<17 at h; omega
  · change 27<18 at h; omega
  · change 27<19 at h; omega
  · change 27<20 at h; omega
  · change 27<21 at h; omega
  · change 27<22 at h; omega
  · change 27<23 at h; omega
  · change 27<24 at h; omega
  · change 27<25 at h; omega
  · change 27<26 at h; omega
  · change 27<27 at h; omega
  · exact c27_28
  · exact c27_29
  · exact c27_30

end Symconf93
