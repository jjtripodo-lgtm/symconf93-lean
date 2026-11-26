module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w10_11 : List LocalWitness31 := []
private theorem c10_11 : CellCovers31 10 11 := by
  have H : (w10_11.all (validWitness31 proto5) && doubleCoverage31 w10_11 10 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_12 : List LocalWitness31 := [⟨8459265,43,false,10⟩,⟨8524801,15,false,10⟩,⟨33690625,77,false,10⟩,⟨75502593,90,true,12⟩,⟨134484993,81,false,10⟩,⟨268571649,89,false,10⟩]
private theorem c10_12 : CellCovers31 10 12 := by
  have H : (w10_12.all (validWitness31 proto5) && doubleCoverage31 w10_12 10 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_13 : List LocalWitness31 := [⟨566273,31,true,15⟩,⟨664577,10,true,19⟩,⟨16819201,72,true,15⟩,⟨17310721,17,false,10⟩,⟨33694721,76,false,10⟩,⟨553657345,89,true,0⟩]
private theorem c10_13 : CellCovers31 10 13 := by
  have H : (w10_13.all (validWitness31 proto5) && doubleCoverage31 w10_13 10 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_14 : List LocalWitness31 := [⟨607233,51,false,14⟩,⟨8471553,63,true,16⟩,⟨37766145,61,false,22⟩,⟨41960449,73,false,23⟩,⟨75514881,80,false,23⟩,⟨545276929,81,true,0⟩]
private theorem c10_14 : CellCovers31 10 14 := by
  have H : (w10_14.all (validWitness31 proto5) && doubleCoverage31 w10_14 10 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_15 : List LocalWitness31 := [⟨4490241,34,false,15⟩,⟨17073153,64,true,18⟩,⟨134513665,80,true,18⟩,⟨537166849,90,false,29⟩]
private theorem c10_15 : CellCovers31 10 15 := by
  have H : (w10_15.all (validWitness31 proto5) && doubleCoverage31 w10_15 10 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_16 : List LocalWitness31 := [⟨8979457,36,false,16⟩,⟨17368065,54,false,16⟩,⟨134546433,73,true,18⟩,⟨134808577,61,true,19⟩,⟨285279233,76,true,0⟩,⟨553714689,77,true,0⟩]
private theorem c10_16 : CellCovers31 10 16 := by
  have H : (w10_16.all (validWitness31 proto5) && doubleCoverage31 w10_16 10 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_17 : List LocalWitness31 := [⟨9044993,11,false,17⟩,⟨37880833,54,true,25⟩,⟨75629569,64,false,23⟩,⟨272761857,17,true,0⟩,⟨335676417,72,false,26⟩]
private theorem c10_17 : CellCovers31 10 17 := by
  have H : (w10_17.all (validWitness31 proto5) && doubleCoverage31 w10_17 10 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_18 : List LocalWitness31 := [⟨21234689,11,true,24⟩,⟨38011905,36,true,25⟩,⟨168035329,63,false,25⟩,⟨553911297,15,true,0⟩,⟨570688513,43,true,0⟩]
private theorem c10_18 : CellCovers31 10 18 := by
  have H : (w10_18.all (validWitness31 proto5) && doubleCoverage31 w10_18 10 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_19 : List LocalWitness31 := [⟨76022785,34,true,26⟩]
private theorem c10_19 : CellCovers31 10 19 := by
  have H : (w10_19.all (validWitness31 proto5) && doubleCoverage31 w10_19 10 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_20 : List LocalWitness31 := []
private theorem c10_20 : CellCovers31 10 20 := by
  have H : (w10_20.all (validWitness31 proto5) && doubleCoverage31 w10_20 10 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_21 : List LocalWitness31 := []
private theorem c10_21 : CellCovers31 10 21 := by
  have H : (w10_21.all (validWitness31 proto5) && doubleCoverage31 w10_21 10 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_22 : List LocalWitness31 := [⟨171967489,51,true,27⟩,⟨289408001,10,false,22⟩,⟨339739649,31,false,26⟩]
private theorem c10_22 : CellCovers31 10 22 := by
  have H : (w10_22.all (validWitness31 proto5) && doubleCoverage31 w10_22 10 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_23 : List LocalWitness31 := []
private theorem c10_23 : CellCovers31 10 23 := by
  have H : (w10_23.all (validWitness31 proto5) && doubleCoverage31 w10_23 10 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_24 : List LocalWitness31 := []
private theorem c10_24 : CellCovers31 10 24 := by
  have H : (w10_24.all (validWitness31 proto5) && doubleCoverage31 w10_24 10 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_25 : List LocalWitness31 := []
private theorem c10_25 : CellCovers31 10 25 := by
  have H : (w10_25.all (validWitness31 proto5) && doubleCoverage31 w10_25 10 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_26 : List LocalWitness31 := []
private theorem c10_26 : CellCovers31 10 26 := by
  have H : (w10_26.all (validWitness31 proto5) && doubleCoverage31 w10_26 10 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_27 : List LocalWitness31 := []
private theorem c10_27 : CellCovers31 10 27 := by
  have H : (w10_27.all (validWitness31 proto5) && doubleCoverage31 w10_27 10 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_28 : List LocalWitness31 := []
private theorem c10_28 : CellCovers31 10 28 := by
  have H : (w10_28.all (validWitness31 proto5) && doubleCoverage31 w10_28 10 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_29 : List LocalWitness31 := []
private theorem c10_29 : CellCovers31 10 29 := by
  have H : (w10_29.all (validWitness31 proto5) && doubleCoverage31 w10_29 10 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w10_30 : List LocalWitness31 := []
private theorem c10_30 : CellCovers31 10 30 := by
  have H : (w10_30.all (validWitness31 proto5) && doubleCoverage31 w10_30 10 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row10 (v : Fin 31) (h : 10<v.val) : CellCovers31 10 v.val := by
  fin_cases v
  · change 10<0 at h; omega
  · change 10<1 at h; omega
  · change 10<2 at h; omega
  · change 10<3 at h; omega
  · change 10<4 at h; omega
  · change 10<5 at h; omega
  · change 10<6 at h; omega
  · change 10<7 at h; omega
  · change 10<8 at h; omega
  · change 10<9 at h; omega
  · change 10<10 at h; omega
  · exact c10_11
  · exact c10_12
  · exact c10_13
  · exact c10_14
  · exact c10_15
  · exact c10_16
  · exact c10_17
  · exact c10_18
  · exact c10_19
  · exact c10_20
  · exact c10_21
  · exact c10_22
  · exact c10_23
  · exact c10_24
  · exact c10_25
  · exact c10_26
  · exact c10_27
  · exact c10_28
  · exact c10_29
  · exact c10_30

end Symconf93
