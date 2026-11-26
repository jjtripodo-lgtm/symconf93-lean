module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w18_19 : List LocalWitness31 := []
private theorem c18_19 : CellCovers31 18 19 := by
  have H : (w18_19.all (validWitness31 proto5) && doubleCoverage31 w18_19 18 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_20 : List LocalWitness31 := []
private theorem c18_20 : CellCovers31 18 20 := by
  have H : (w18_20.all (validWitness31 proto5) && doubleCoverage31 w18_20 18 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_21 : List LocalWitness31 := []
private theorem c18_21 : CellCovers31 18 21 := by
  have H : (w18_21.all (validWitness31 proto5) && doubleCoverage31 w18_21 18 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_22 : List LocalWitness31 := []
private theorem c18_22 : CellCovers31 18 22 := by
  have H : (w18_22.all (validWitness31 proto5) && doubleCoverage31 w18_22 18 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_23 : List LocalWitness31 := []
private theorem c18_23 : CellCovers31 18 23 := by
  have H : (w18_23.all (validWitness31 proto5) && doubleCoverage31 w18_23 18 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_24 : List LocalWitness31 := []
private theorem c18_24 : CellCovers31 18 24 := by
  have H : (w18_24.all (validWitness31 proto5) && doubleCoverage31 w18_24 18 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_25 : List LocalWitness31 := []
private theorem c18_25 : CellCovers31 18 25 := by
  have H : (w18_25.all (validWitness31 proto5) && doubleCoverage31 w18_25 18 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_26 : List LocalWitness31 := []
private theorem c18_26 : CellCovers31 18 26 := by
  have H : (w18_26.all (validWitness31 proto5) && doubleCoverage31 w18_26 18 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_27 : List LocalWitness31 := []
private theorem c18_27 : CellCovers31 18 27 := by
  have H : (w18_27.all (validWitness31 proto5) && doubleCoverage31 w18_27 18 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_28 : List LocalWitness31 := []
private theorem c18_28 : CellCovers31 18 28 := by
  have H : (w18_28.all (validWitness31 proto5) && doubleCoverage31 w18_28 18 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_29 : List LocalWitness31 := []
private theorem c18_29 : CellCovers31 18 29 := by
  have H : (w18_29.all (validWitness31 proto5) && doubleCoverage31 w18_29 18 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w18_30 : List LocalWitness31 := []
private theorem c18_30 : CellCovers31 18 30 := by
  have H : (w18_30.all (validWitness31 proto5) && doubleCoverage31 w18_30 18 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row18 (v : Fin 31) (h : 18<v.val) : CellCovers31 18 v.val := by
  fin_cases v
  · change 18<0 at h; omega
  · change 18<1 at h; omega
  · change 18<2 at h; omega
  · change 18<3 at h; omega
  · change 18<4 at h; omega
  · change 18<5 at h; omega
  · change 18<6 at h; omega
  · change 18<7 at h; omega
  · change 18<8 at h; omega
  · change 18<9 at h; omega
  · change 18<10 at h; omega
  · change 18<11 at h; omega
  · change 18<12 at h; omega
  · change 18<13 at h; omega
  · change 18<14 at h; omega
  · change 18<15 at h; omega
  · change 18<16 at h; omega
  · change 18<17 at h; omega
  · change 18<18 at h; omega
  · exact c18_19
  · exact c18_20
  · exact c18_21
  · exact c18_22
  · exact c18_23
  · exact c18_24
  · exact c18_25
  · exact c18_26
  · exact c18_27
  · exact c18_28
  · exact c18_29
  · exact c18_30

end Symconf93
