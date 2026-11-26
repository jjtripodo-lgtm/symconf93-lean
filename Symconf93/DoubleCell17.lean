module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w17_18 : List LocalWitness31 := []
private theorem c17_18 : CellCovers31 17 18 := by
  have H : (w17_18.all (validWitness31 proto5) && doubleCoverage31 w17_18 17 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_19 : List LocalWitness31 := [⟨76152833,3,false,17⟩,⟨277479425,4,false,17⟩]
private theorem c17_19 : CellCovers31 17 19 := by
  have H : (w17_19.all (validWitness31 proto5) && doubleCoverage31 w17_19 17 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_20 : List LocalWitness31 := [⟨168951809,2,false,25⟩,⟨571604993,4,true,0⟩]
private theorem c17_20 : CellCovers31 17 20 := by
  have H : (w17_20.all (validWitness31 proto5) && doubleCoverage31 w17_20 17 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_21 : List LocalWitness31 := [⟨279052289,2,true,23⟩]
private theorem c17_21 : CellCovers31 17 21 := by
  have H : (w17_21.all (validWitness31 proto5) && doubleCoverage31 w17_21 17 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_22 : List LocalWitness31 := [⟨574750721,3,true,0⟩]
private theorem c17_22 : CellCovers31 17 22 := by
  have H : (w17_22.all (validWitness31 proto5) && doubleCoverage31 w17_22 17 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_23 : List LocalWitness31 := []
private theorem c17_23 : CellCovers31 17 23 := by
  have H : (w17_23.all (validWitness31 proto5) && doubleCoverage31 w17_23 17 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_24 : List LocalWitness31 := []
private theorem c17_24 : CellCovers31 17 24 := by
  have H : (w17_24.all (validWitness31 proto5) && doubleCoverage31 w17_24 17 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_25 : List LocalWitness31 := []
private theorem c17_25 : CellCovers31 17 25 := by
  have H : (w17_25.all (validWitness31 proto5) && doubleCoverage31 w17_25 17 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_26 : List LocalWitness31 := []
private theorem c17_26 : CellCovers31 17 26 := by
  have H : (w17_26.all (validWitness31 proto5) && doubleCoverage31 w17_26 17 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_27 : List LocalWitness31 := []
private theorem c17_27 : CellCovers31 17 27 := by
  have H : (w17_27.all (validWitness31 proto5) && doubleCoverage31 w17_27 17 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_28 : List LocalWitness31 := []
private theorem c17_28 : CellCovers31 17 28 := by
  have H : (w17_28.all (validWitness31 proto5) && doubleCoverage31 w17_28 17 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_29 : List LocalWitness31 := []
private theorem c17_29 : CellCovers31 17 29 := by
  have H : (w17_29.all (validWitness31 proto5) && doubleCoverage31 w17_29 17 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w17_30 : List LocalWitness31 := []
private theorem c17_30 : CellCovers31 17 30 := by
  have H : (w17_30.all (validWitness31 proto5) && doubleCoverage31 w17_30 17 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row17 (v : Fin 31) (h : 17<v.val) : CellCovers31 17 v.val := by
  fin_cases v
  · change 17<0 at h; omega
  · change 17<1 at h; omega
  · change 17<2 at h; omega
  · change 17<3 at h; omega
  · change 17<4 at h; omega
  · change 17<5 at h; omega
  · change 17<6 at h; omega
  · change 17<7 at h; omega
  · change 17<8 at h; omega
  · change 17<9 at h; omega
  · change 17<10 at h; omega
  · change 17<11 at h; omega
  · change 17<12 at h; omega
  · change 17<13 at h; omega
  · change 17<14 at h; omega
  · change 17<15 at h; omega
  · change 17<16 at h; omega
  · change 17<17 at h; omega
  · exact c17_18
  · exact c17_19
  · exact c17_20
  · exact c17_21
  · exact c17_22
  · exact c17_23
  · exact c17_24
  · exact c17_25
  · exact c17_26
  · exact c17_27
  · exact c17_28
  · exact c17_29
  · exact c17_30

end Symconf93
