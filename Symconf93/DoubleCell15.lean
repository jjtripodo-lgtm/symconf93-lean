module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w15_16 : List LocalWitness31 := []
private theorem c15_16 : CellCovers31 15 16 := by
  have H : (w15_16.all (validWitness31 proto5) && doubleCoverage31 w15_16 15 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_17 : List LocalWitness31 := [⟨37912577,47,false,15⟩,⟨135430145,57,false,15⟩,⟨270696449,67,false,15⟩,⟨272793601,65,false,15⟩]
private theorem c15_17 : CellCovers31 15 17 := by
  have H : (w15_17.all (validWitness31 proto5) && doubleCoverage31 w15_17 15 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_18 : List LocalWitness31 := [⟨18120705,25,true,20⟩,⟨84180993,27,false,24⟩,⟨135561217,38,true,20⟩,⟨168067073,32,false,25⟩,⟨553943041,65,true,0⟩,⟨570720257,67,true,0⟩]
private theorem c15_18 : CellCovers31 15 18 := by
  have H : (w15_18.all (validWitness31 proto5) && doubleCoverage31 w15_18 15 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_19 : List LocalWitness31 := [⟨19431425,20,false,19⟩,⟨271089665,32,true,21⟩,⟨336101377,38,false,26⟩,⟨604536833,57,true,0⟩]
private theorem c15_19 : CellCovers31 15 19 := by
  have H : (w15_19.all (validWitness31 proto5) && doubleCoverage31 w15_19 15 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_20 : List LocalWitness31 := [⟨273711105,27,true,22⟩]
private theorem c15_20 : CellCovers31 15 20 := by
  have H : (w15_20.all (validWitness31 proto5) && doubleCoverage31 w15_20 15 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_21 : List LocalWitness31 := [⟨555778049,47,true,0⟩]
private theorem c15_21 : CellCovers31 15 21 := by
  have H : (w15_21.all (validWitness31 proto5) && doubleCoverage31 w15_21 15 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_22 : List LocalWitness31 := [⟨171999233,20,true,27⟩,⟨339771393,25,false,26⟩]
private theorem c15_22 : CellCovers31 15 22 := by
  have H : (w15_22.all (validWitness31 proto5) && doubleCoverage31 w15_22 15 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_23 : List LocalWitness31 := []
private theorem c15_23 : CellCovers31 15 23 := by
  have H : (w15_23.all (validWitness31 proto5) && doubleCoverage31 w15_23 15 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_24 : List LocalWitness31 := []
private theorem c15_24 : CellCovers31 15 24 := by
  have H : (w15_24.all (validWitness31 proto5) && doubleCoverage31 w15_24 15 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_25 : List LocalWitness31 := []
private theorem c15_25 : CellCovers31 15 25 := by
  have H : (w15_25.all (validWitness31 proto5) && doubleCoverage31 w15_25 15 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_26 : List LocalWitness31 := []
private theorem c15_26 : CellCovers31 15 26 := by
  have H : (w15_26.all (validWitness31 proto5) && doubleCoverage31 w15_26 15 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_27 : List LocalWitness31 := []
private theorem c15_27 : CellCovers31 15 27 := by
  have H : (w15_27.all (validWitness31 proto5) && doubleCoverage31 w15_27 15 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_28 : List LocalWitness31 := []
private theorem c15_28 : CellCovers31 15 28 := by
  have H : (w15_28.all (validWitness31 proto5) && doubleCoverage31 w15_28 15 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_29 : List LocalWitness31 := []
private theorem c15_29 : CellCovers31 15 29 := by
  have H : (w15_29.all (validWitness31 proto5) && doubleCoverage31 w15_29 15 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w15_30 : List LocalWitness31 := []
private theorem c15_30 : CellCovers31 15 30 := by
  have H : (w15_30.all (validWitness31 proto5) && doubleCoverage31 w15_30 15 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row15 (v : Fin 31) (h : 15<v.val) : CellCovers31 15 v.val := by
  fin_cases v
  · change 15<0 at h; omega
  · change 15<1 at h; omega
  · change 15<2 at h; omega
  · change 15<3 at h; omega
  · change 15<4 at h; omega
  · change 15<5 at h; omega
  · change 15<6 at h; omega
  · change 15<7 at h; omega
  · change 15<8 at h; omega
  · change 15<9 at h; omega
  · change 15<10 at h; omega
  · change 15<11 at h; omega
  · change 15<12 at h; omega
  · change 15<13 at h; omega
  · change 15<14 at h; omega
  · change 15<15 at h; omega
  · exact c15_16
  · exact c15_17
  · exact c15_18
  · exact c15_19
  · exact c15_20
  · exact c15_21
  · exact c15_22
  · exact c15_23
  · exact c15_24
  · exact c15_25
  · exact c15_26
  · exact c15_27
  · exact c15_28
  · exact c15_29
  · exact c15_30

end Symconf93
