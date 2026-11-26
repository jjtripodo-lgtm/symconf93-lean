module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w13_14 : List LocalWitness31 := []
private theorem c13_14 : CellCovers31 13 14 := by
  have H : (w13_14.all (validWitness31 proto5) && doubleCoverage31 w13_14 13 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_15 : List LocalWitness31 := [⟨17342465,39,false,13⟩,⟨18915329,29,false,13⟩,⟨151035905,87,false,13⟩]
private theorem c13_15 : CellCovers31 13 15 := by
  have H : (w13_15.all (validWitness31 proto5) && doubleCoverage31 w13_15 13 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_16 : List LocalWitness31 := [⟨34676737,40,false,13⟩,⟨35725313,33,false,13⟩,⟨42016769,35,false,23⟩,⟨136388609,69,false,13⟩,⟨167845889,85,false,25⟩]
private theorem c13_16 : CellCovers31 13 16 := by
  have H : (w13_16.all (validWitness31 proto5) && doubleCoverage31 w13_16 13 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_17 : List LocalWitness31 := [⟨34742273,12,true,20⟩,⟨269099009,85,true,19⟩,⟨276963329,69,true,0⟩,⟨538058753,87,true,0⟩]
private theorem c13_17 : CellCovers31 13 17 := by
  have H : (w13_17.all (validWitness31 proto5) && doubleCoverage31 w13_17 13 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_18 : List LocalWitness31 := []
private theorem c13_18 : CellCovers31 13 18 := by
  have H : (w13_18.all (validWitness31 proto5) && doubleCoverage31 w13_18 13 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_19 : List LocalWitness31 := [⟨19406849,0,false,19⟩,⟨151527425,12,false,24⟩,⟨271065089,35,true,21⟩,⟨277356545,33,true,0⟩,⟨285745153,40,true,0⟩]
private theorem c13_19 : CellCovers31 13 19 := by
  have H : (w13_19.all (validWitness31 proto5) && doubleCoverage31 w13_19 13 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_20 : List LocalWitness31 := [⟨42999809,0,true,25⟩,⟨546316289,29,true,0⟩,⟨571482113,39,true,0⟩]
private theorem c13_20 : CellCovers31 13 20 := by
  have H : (w13_20.all (validWitness31 proto5) && doubleCoverage31 w13_20 13 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_21 : List LocalWitness31 := []
private theorem c13_21 : CellCovers31 13 21 := by
  have H : (w13_21.all (validWitness31 proto5) && doubleCoverage31 w13_21 13 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_22 : List LocalWitness31 := []
private theorem c13_22 : CellCovers31 13 22 := by
  have H : (w13_22.all (validWitness31 proto5) && doubleCoverage31 w13_22 13 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_23 : List LocalWitness31 := []
private theorem c13_23 : CellCovers31 13 23 := by
  have H : (w13_23.all (validWitness31 proto5) && doubleCoverage31 w13_23 13 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_24 : List LocalWitness31 := []
private theorem c13_24 : CellCovers31 13 24 := by
  have H : (w13_24.all (validWitness31 proto5) && doubleCoverage31 w13_24 13 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_25 : List LocalWitness31 := []
private theorem c13_25 : CellCovers31 13 25 := by
  have H : (w13_25.all (validWitness31 proto5) && doubleCoverage31 w13_25 13 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_26 : List LocalWitness31 := []
private theorem c13_26 : CellCovers31 13 26 := by
  have H : (w13_26.all (validWitness31 proto5) && doubleCoverage31 w13_26 13 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_27 : List LocalWitness31 := []
private theorem c13_27 : CellCovers31 13 27 := by
  have H : (w13_27.all (validWitness31 proto5) && doubleCoverage31 w13_27 13 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_28 : List LocalWitness31 := []
private theorem c13_28 : CellCovers31 13 28 := by
  have H : (w13_28.all (validWitness31 proto5) && doubleCoverage31 w13_28 13 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_29 : List LocalWitness31 := []
private theorem c13_29 : CellCovers31 13 29 := by
  have H : (w13_29.all (validWitness31 proto5) && doubleCoverage31 w13_29 13 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w13_30 : List LocalWitness31 := []
private theorem c13_30 : CellCovers31 13 30 := by
  have H : (w13_30.all (validWitness31 proto5) && doubleCoverage31 w13_30 13 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row13 (v : Fin 31) (h : 13<v.val) : CellCovers31 13 v.val := by
  fin_cases v
  · change 13<0 at h; omega
  · change 13<1 at h; omega
  · change 13<2 at h; omega
  · change 13<3 at h; omega
  · change 13<4 at h; omega
  · change 13<5 at h; omega
  · change 13<6 at h; omega
  · change 13<7 at h; omega
  · change 13<8 at h; omega
  · change 13<9 at h; omega
  · change 13<10 at h; omega
  · change 13<11 at h; omega
  · change 13<12 at h; omega
  · change 13<13 at h; omega
  · exact c13_14
  · exact c13_15
  · exact c13_16
  · exact c13_17
  · exact c13_18
  · exact c13_19
  · exact c13_20
  · exact c13_21
  · exact c13_22
  · exact c13_23
  · exact c13_24
  · exact c13_25
  · exact c13_26
  · exact c13_27
  · exact c13_28
  · exact c13_29
  · exact c13_30

end Symconf93
