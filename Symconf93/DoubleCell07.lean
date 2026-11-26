module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w07_08 : List LocalWitness31 := []
private theorem c07_08 : CellCovers31 7 8 := by
  have H : (w07_08.all (validWitness31 proto5) && doubleCoverage31 w07_08 7 8)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_09 : List LocalWitness31 := [⟨2105985,11,false,7⟩,⟨8393345,55,false,7⟩,⟨8397441,63,false,7⟩,⟨35652225,78,true,9⟩,⟨67142273,56,false,7⟩,⟨134222465,38,false,7⟩,⟨134251137,41,false,7⟩,⟨136315521,16,true,9⟩,⟨268444289,32,false,7⟩,⟨268468865,35,false,7⟩,⟨276824705,53,true,9⟩]
private theorem c07_09 : CellCovers31 7 9 := by
  have H : (w07_09.all (validWitness31 proto5) && doubleCoverage31 w07_09 7 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_10 : List LocalWitness31 := [⟨70785,20,true,12⟩,⟨267393,0,true,12⟩,⟨328833,29,true,18⟩,⟨4457601,45,true,10⟩,⟨8393857,42,true,12⟩,⟨134222977,57,true,12⟩,⟨134251649,58,false,7⟩,⟨138413185,59,true,10⟩,⟨167773313,67,false,25⟩,⟨536904833,53,false,29⟩,⟨545260673,35,true,0⟩,⟨570426497,32,true,0⟩]
private theorem c07_10 : CellCovers31 7 10 := by
  have H : (w07_10.all (validWitness31 proto5) && doubleCoverage31 w07_10 7 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_11 : List LocalWitness31 := [⟨75905,25,false,11⟩,⟨8398977,43,true,13⟩,⟨41945217,84,false,23⟩,⟨67242113,60,false,7⟩,⟨268445825,67,true,13⟩,⟨268503169,59,false,28⟩,⟨276826241,58,true,0⟩,⟨335546497,57,false,26⟩,⟨537004161,16,false,29⟩,⟨545261697,41,true,0⟩,⟨603981953,38,true,0⟩]
private theorem c07_11 : CellCovers31 7 11 := by
  have H : (w07_11.all (validWitness31 proto5) && doubleCoverage31 w07_11 7 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_12 : List LocalWitness31 := [⟨331905,39,true,18⟩,⟨2134145,54,true,15⟩,⟨2363521,17,true,21⟩,⟨4460673,44,true,22⟩,⟨5247105,46,true,22⟩,⟨10489985,62,false,21⟩,⟨136319105,60,true,0⟩,⟨545263745,56,true,0⟩]
private theorem c07_12 : CellCovers31 7 12 := by
  have H : (w07_12.all (validWitness31 proto5) && doubleCoverage31 w07_12 7 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_13 : List LocalWitness31 := [⟨2171009,64,false,13⟩,⟨134258817,84,true,15⟩,⟨537010305,78,false,29⟩]
private theorem c07_13 : CellCovers31 7 13 := by
  have H : (w07_13.all (validWitness31 proto5) && doubleCoverage31 w07_13 7 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_14 : List LocalWitness31 := []
private theorem c07_14 : CellCovers31 7 14 := by
  have H : (w07_14.all (validWitness31 proto5) && doubleCoverage31 w07_14 7 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_15 : List LocalWitness31 := [⟨1212545,71,false,15⟩,⟨67272833,62,true,17⟩,⟨167805057,43,false,25⟩,⟨335577217,42,false,26⟩,⟨570458241,63,true,0⟩,⟨604012673,55,true,0⟩]
private theorem c07_15 : CellCovers31 7 15 := by
  have H : (w07_15.all (validWitness31 proto5) && doubleCoverage31 w07_15 7 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_16 : List LocalWitness31 := [⟨2424961,72,false,16⟩,⟨67436673,46,false,16⟩,⟨68223105,44,false,16⟩,⟨269549697,45,false,28⟩]
private theorem c07_16 : CellCovers31 7 16 := by
  have H : (w07_16.all (validWitness31 proto5) && doubleCoverage31 w07_16 7 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_17 : List LocalWitness31 := [⟨5374081,72,true,22⟩,⟨37879937,64,true,25⟩,⟨68288641,17,false,17⟩,⟨75628673,54,false,23⟩,⟨570556545,11,true,0⟩]
private theorem c07_17 : CellCovers31 7 17 := by
  have H : (w07_17.all (validWitness31 proto5) && doubleCoverage31 w07_17 7 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_18 : List LocalWitness31 := [⟨10748033,71,true,23⟩]
private theorem c07_18 : CellCovers31 7 18 := by
  have H : (w07_18.all (validWitness31 proto5) && doubleCoverage31 w07_18 7 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_19 : List LocalWitness31 := []
private theorem c07_19 : CellCovers31 7 19 := by
  have H : (w07_19.all (validWitness31 proto5) && doubleCoverage31 w07_19 7 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_20 : List LocalWitness31 := [⟨72351873,39,false,20⟩,⟨273678465,29,false,20⟩,⟨336593025,0,false,26⟩]
private theorem c07_20 : CellCovers31 7 20 := by
  have H : (w07_20.all (validWitness31 proto5) && doubleCoverage31 w07_20 7 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_21 : List LocalWitness31 := []
private theorem c07_21 : CellCovers31 7 21 := by
  have H : (w07_21.all (validWitness31 proto5) && doubleCoverage31 w07_21 7 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_22 : List LocalWitness31 := [⟨171966593,25,true,27⟩,⟨339738753,20,false,26⟩]
private theorem c07_22 : CellCovers31 7 22 := by
  have H : (w07_22.all (validWitness31 proto5) && doubleCoverage31 w07_22 7 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_23 : List LocalWitness31 := []
private theorem c07_23 : CellCovers31 7 23 := by
  have H : (w07_23.all (validWitness31 proto5) && doubleCoverage31 w07_23 7 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_24 : List LocalWitness31 := []
private theorem c07_24 : CellCovers31 7 24 := by
  have H : (w07_24.all (validWitness31 proto5) && doubleCoverage31 w07_24 7 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_25 : List LocalWitness31 := []
private theorem c07_25 : CellCovers31 7 25 := by
  have H : (w07_25.all (validWitness31 proto5) && doubleCoverage31 w07_25 7 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_26 : List LocalWitness31 := []
private theorem c07_26 : CellCovers31 7 26 := by
  have H : (w07_26.all (validWitness31 proto5) && doubleCoverage31 w07_26 7 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_27 : List LocalWitness31 := []
private theorem c07_27 : CellCovers31 7 27 := by
  have H : (w07_27.all (validWitness31 proto5) && doubleCoverage31 w07_27 7 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_28 : List LocalWitness31 := []
private theorem c07_28 : CellCovers31 7 28 := by
  have H : (w07_28.all (validWitness31 proto5) && doubleCoverage31 w07_28 7 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_29 : List LocalWitness31 := []
private theorem c07_29 : CellCovers31 7 29 := by
  have H : (w07_29.all (validWitness31 proto5) && doubleCoverage31 w07_29 7 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w07_30 : List LocalWitness31 := []
private theorem c07_30 : CellCovers31 7 30 := by
  have H : (w07_30.all (validWitness31 proto5) && doubleCoverage31 w07_30 7 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row07 (v : Fin 31) (h : 7<v.val) : CellCovers31 7 v.val := by
  fin_cases v
  · change 7<0 at h; omega
  · change 7<1 at h; omega
  · change 7<2 at h; omega
  · change 7<3 at h; omega
  · change 7<4 at h; omega
  · change 7<5 at h; omega
  · change 7<6 at h; omega
  · change 7<7 at h; omega
  · exact c07_08
  · exact c07_09
  · exact c07_10
  · exact c07_11
  · exact c07_12
  · exact c07_13
  · exact c07_14
  · exact c07_15
  · exact c07_16
  · exact c07_17
  · exact c07_18
  · exact c07_19
  · exact c07_20
  · exact c07_21
  · exact c07_22
  · exact c07_23
  · exact c07_24
  · exact c07_25
  · exact c07_26
  · exact c07_27
  · exact c07_28
  · exact c07_29
  · exact c07_30

end Symconf93
