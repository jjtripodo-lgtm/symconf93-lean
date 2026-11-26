module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w29_30 : List LocalWitness31 := []
private theorem c29_30 : CellCovers31 29 30 := by
  have H : (w29_30.all (validWitness31 proto5) && doubleCoverage31 w29_30 29 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row29 (v : Fin 31) (h : 29<v.val) : CellCovers31 29 v.val := by
  fin_cases v
  · change 29<0 at h; omega
  · change 29<1 at h; omega
  · change 29<2 at h; omega
  · change 29<3 at h; omega
  · change 29<4 at h; omega
  · change 29<5 at h; omega
  · change 29<6 at h; omega
  · change 29<7 at h; omega
  · change 29<8 at h; omega
  · change 29<9 at h; omega
  · change 29<10 at h; omega
  · change 29<11 at h; omega
  · change 29<12 at h; omega
  · change 29<13 at h; omega
  · change 29<14 at h; omega
  · change 29<15 at h; omega
  · change 29<16 at h; omega
  · change 29<17 at h; omega
  · change 29<18 at h; omega
  · change 29<19 at h; omega
  · change 29<20 at h; omega
  · change 29<21 at h; omega
  · change 29<22 at h; omega
  · change 29<23 at h; omega
  · change 29<24 at h; omega
  · change 29<25 at h; omega
  · change 29<26 at h; omega
  · change 29<27 at h; omega
  · change 29<28 at h; omega
  · change 29<29 at h; omega
  · exact c29_30

end Symconf93
