module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w19_20 : List LocalWitness31 := []
private theorem c19_20 : CellCovers31 19 20 := by
  have H : (w19_20.all (validWitness31 proto5) && doubleCoverage31 w19_20 19 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_21 : List LocalWitness31 := []
private theorem c19_21 : CellCovers31 19 21 := by
  have H : (w19_21.all (validWitness31 proto5) && doubleCoverage31 w19_21 19 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_22 : List LocalWitness31 := []
private theorem c19_22 : CellCovers31 19 22 := by
  have H : (w19_22.all (validWitness31 proto5) && doubleCoverage31 w19_22 19 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_23 : List LocalWitness31 := []
private theorem c19_23 : CellCovers31 19 23 := by
  have H : (w19_23.all (validWitness31 proto5) && doubleCoverage31 w19_23 19 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_24 : List LocalWitness31 := []
private theorem c19_24 : CellCovers31 19 24 := by
  have H : (w19_24.all (validWitness31 proto5) && doubleCoverage31 w19_24 19 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_25 : List LocalWitness31 := []
private theorem c19_25 : CellCovers31 19 25 := by
  have H : (w19_25.all (validWitness31 proto5) && doubleCoverage31 w19_25 19 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_26 : List LocalWitness31 := []
private theorem c19_26 : CellCovers31 19 26 := by
  have H : (w19_26.all (validWitness31 proto5) && doubleCoverage31 w19_26 19 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_27 : List LocalWitness31 := []
private theorem c19_27 : CellCovers31 19 27 := by
  have H : (w19_27.all (validWitness31 proto5) && doubleCoverage31 w19_27 19 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_28 : List LocalWitness31 := []
private theorem c19_28 : CellCovers31 19 28 := by
  have H : (w19_28.all (validWitness31 proto5) && doubleCoverage31 w19_28 19 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_29 : List LocalWitness31 := []
private theorem c19_29 : CellCovers31 19 29 := by
  have H : (w19_29.all (validWitness31 proto5) && doubleCoverage31 w19_29 19 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w19_30 : List LocalWitness31 := []
private theorem c19_30 : CellCovers31 19 30 := by
  have H : (w19_30.all (validWitness31 proto5) && doubleCoverage31 w19_30 19 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row19 (v : Fin 31) (h : 19<v.val) : CellCovers31 19 v.val := by
  fin_cases v
  · change 19<0 at h; omega
  · change 19<1 at h; omega
  · change 19<2 at h; omega
  · change 19<3 at h; omega
  · change 19<4 at h; omega
  · change 19<5 at h; omega
  · change 19<6 at h; omega
  · change 19<7 at h; omega
  · change 19<8 at h; omega
  · change 19<9 at h; omega
  · change 19<10 at h; omega
  · change 19<11 at h; omega
  · change 19<12 at h; omega
  · change 19<13 at h; omega
  · change 19<14 at h; omega
  · change 19<15 at h; omega
  · change 19<16 at h; omega
  · change 19<17 at h; omega
  · change 19<18 at h; omega
  · change 19<19 at h; omega
  · exact c19_20
  · exact c19_21
  · exact c19_22
  · exact c19_23
  · exact c19_24
  · exact c19_25
  · exact c19_26
  · exact c19_27
  · exact c19_28
  · exact c19_29
  · exact c19_30

end Symconf93
