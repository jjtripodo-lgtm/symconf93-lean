module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w06_07 : List LocalWitness31 := []
private theorem c06_07 : CellCovers31 6 7 := by
  have H : (w06_07.all (validWitness31 proto5) && doubleCoverage31 w06_07 6 7)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_08 : List LocalWitness31 := [⟨35137,19,false,6⟩,⟨139585,8,false,6⟩,⟨264513,0,false,6⟩,⟨295233,35,true,8⟩,⟨557377,41,true,8⟩,⟨1081665,56,true,8⟩,⟨2228545,73,true,8⟩,⟨4456769,81,true,8⟩,⟨4718913,88,true,8⟩,⟨17826113,84,true,8⟩,⟨71303489,66,true,8⟩,⟨134220097,21,false,6⟩,⟨134226241,9,false,6⟩,⟨138412353,52,true,8⟩,⟨150995265,30,true,8⟩,⟨268443969,27,false,6⟩,⟨270532929,29,true,8⟩,⟨285212993,26,true,8⟩]
private theorem c06_08 : CellCovers31 6 8 := by
  have H : (w06_08.all (validWitness31 proto5) && doubleCoverage31 w06_08 6 8)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_09 : List LocalWitness31 := [⟨82497,47,true,16⟩,⟨526913,1,true,11⟩,⟨655937,18,true,19⟩,⟨2105921,36,false,6⟩,⟨2114113,54,false,6⟩,⟨2228801,61,true,9⟩,⟨16794177,64,false,6⟩,⟨67633729,17,true,9⟩,⟨83886657,65,false,24⟩,⟨134220353,28,true,11⟩,⟨536879681,26,false,29⟩,⟨536937025,29,false,29⟩,⟨553648705,27,true,0⟩]
private theorem c06_09 : CellCovers31 6 9 := by
  have H : (w06_09.all (validWitness31 proto5) && doubleCoverage31 w06_09 6 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_10 : List LocalWitness31 := [⟨42049,24,true,15⟩,⟨164929,49,true,17⟩,⟨296001,33,true,18⟩,⟨656449,16,true,19⟩,⟨4326465,60,true,10⟩,⟨20972609,78,false,22⟩,⟨67634241,44,true,10⟩,⟨75498561,69,false,23⟩,⟨83887169,68,false,24⟩,⟨335545409,28,false,26⟩,⟨536880193,30,false,29⟩,⟨536904769,52,false,29⟩,⟨553649217,9,true,0⟩,⟨603980865,21,true,0⟩]
private theorem c06_10 : CellCovers31 6 10 := by
  have H : (w06_10.all (validWitness31 proto5) && doubleCoverage31 w06_10 6 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_11 : List LocalWitness31 := [⟨280641,12,false,11⟩,⟨297025,40,true,18⟩,⟨8398913,15,true,13⟩,⟨134228033,68,true,13⟩,⟨134236225,69,true,14⟩,⟨134481985,44,false,27⟩,⟨268445761,65,true,13⟩,⟨268699713,17,false,28⟩,⟨536905793,66,false,29⟩]
private theorem c06_11 : CellCovers31 6 11 := by
  have H : (w06_11.all (validWitness31 proto5) && doubleCoverage31 w06_11 6 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_12 : List LocalWitness31 := []
private theorem c06_12 : CellCovers31 6 12 := by
  have H : (w06_12.all (validWitness31 proto5) && doubleCoverage31 w06_12 6 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_13 : List LocalWitness31 := [⟨134258753,78,true,15⟩,⟨276832321,64,true,0⟩,⟨537010241,84,false,29⟩]
private theorem c06_13 : CellCovers31 6 13 := by
  have H : (w06_13.all (validWitness31 proto5) && doubleCoverage31 w06_13 6 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_14 : List LocalWitness31 := [⟨606273,74,false,14⟩,⟨2375745,76,true,21⟩,⟨2637889,77,true,21⟩,⟨83902529,15,false,24⟩]
private theorem c06_14 : CellCovers31 6 14 := by
  have H : (w06_14.all (validWitness31 proto5) && doubleCoverage31 w06_14 6 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_15 : List LocalWitness31 := [⟨1343553,86,true,20⟩,⟨135299137,60,false,27⟩,⟨537165889,88,false,29⟩,⟨537428033,81,false,29⟩]
private theorem c06_15 : CellCovers31 6 15 := by
  have H : (w06_15.all (validWitness31 proto5) && doubleCoverage31 w06_15 6 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_16 : List LocalWitness31 := [⟨8716353,77,false,16⟩,⟨8978497,76,false,16⟩,⟨269549633,61,false,28⟩,⟨276889665,54,true,0⟩,⟨285278273,36,true,0⟩,⟨537985089,73,false,29⟩]
private theorem c06_16 : CellCovers31 6 16 := by
  have H : (w06_16.all (validWitness31 proto5) && doubleCoverage31 w06_16 6 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_17 : List LocalWitness31 := [⟨4849729,86,false,17⟩,⟨541196353,56,false,29⟩]
private theorem c06_17 : CellCovers31 6 17 := by
  have H : (w06_17.all (validWitness31 proto5) && doubleCoverage31 w06_17 6 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_18 : List LocalWitness31 := [⟨10747969,74,true,23⟩,⟨135528513,16,false,18⟩,⟨269746241,18,false,18⟩,⟨335806529,1,false,26⟩,⟨541327425,41,false,29⟩]
private theorem c06_18 : CellCovers31 6 18 := by
  have H : (w06_18.all (validWitness31 proto5) && doubleCoverage31 w06_18 6 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_19 : List LocalWitness31 := [⟨71827521,40,false,19⟩,⟨76021825,12,true,26⟩,⟨138936385,33,false,19⟩,⟨541589569,35,false,29⟩,⟨604504129,0,true,0⟩]
private theorem c06_19 : CellCovers31 6 19 := by
  have H : (w06_19.all (validWitness31 proto5) && doubleCoverage31 w06_19 6 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_20 : List LocalWitness31 := [⟨139460673,49,false,20⟩,⟨554696769,8,true,0⟩]
private theorem c06_20 : CellCovers31 6 20 := by
  have H : (w06_20.all (validWitness31 proto5) && doubleCoverage31 w06_20 6 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_21 : List LocalWitness31 := [⟨278921281,47,false,21⟩]
private theorem c06_21 : CellCovers31 6 21 := by
  have H : (w06_21.all (validWitness31 proto5) && doubleCoverage31 w06_21 6 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_22 : List LocalWitness31 := [⟨155189313,24,false,22⟩,⟨608174145,19,true,0⟩]
private theorem c06_22 : CellCovers31 6 22 := by
  have H : (w06_22.all (validWitness31 proto5) && doubleCoverage31 w06_22 6 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_23 : List LocalWitness31 := []
private theorem c06_23 : CellCovers31 6 23 := by
  have H : (w06_23.all (validWitness31 proto5) && doubleCoverage31 w06_23 6 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_24 : List LocalWitness31 := []
private theorem c06_24 : CellCovers31 6 24 := by
  have H : (w06_24.all (validWitness31 proto5) && doubleCoverage31 w06_24 6 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_25 : List LocalWitness31 := []
private theorem c06_25 : CellCovers31 6 25 := by
  have H : (w06_25.all (validWitness31 proto5) && doubleCoverage31 w06_25 6 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_26 : List LocalWitness31 := []
private theorem c06_26 : CellCovers31 6 26 := by
  have H : (w06_26.all (validWitness31 proto5) && doubleCoverage31 w06_26 6 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_27 : List LocalWitness31 := []
private theorem c06_27 : CellCovers31 6 27 := by
  have H : (w06_27.all (validWitness31 proto5) && doubleCoverage31 w06_27 6 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_28 : List LocalWitness31 := []
private theorem c06_28 : CellCovers31 6 28 := by
  have H : (w06_28.all (validWitness31 proto5) && doubleCoverage31 w06_28 6 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_29 : List LocalWitness31 := []
private theorem c06_29 : CellCovers31 6 29 := by
  have H : (w06_29.all (validWitness31 proto5) && doubleCoverage31 w06_29 6 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w06_30 : List LocalWitness31 := []
private theorem c06_30 : CellCovers31 6 30 := by
  have H : (w06_30.all (validWitness31 proto5) && doubleCoverage31 w06_30 6 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row06 (v : Fin 31) (h : 6<v.val) : CellCovers31 6 v.val := by
  fin_cases v
  · change 6<0 at h; omega
  · change 6<1 at h; omega
  · change 6<2 at h; omega
  · change 6<3 at h; omega
  · change 6<4 at h; omega
  · change 6<5 at h; omega
  · change 6<6 at h; omega
  · exact c06_07
  · exact c06_08
  · exact c06_09
  · exact c06_10
  · exact c06_11
  · exact c06_12
  · exact c06_13
  · exact c06_14
  · exact c06_15
  · exact c06_16
  · exact c06_17
  · exact c06_18
  · exact c06_19
  · exact c06_20
  · exact c06_21
  · exact c06_22
  · exact c06_23
  · exact c06_24
  · exact c06_25
  · exact c06_26
  · exact c06_27
  · exact c06_28
  · exact c06_29
  · exact c06_30

end Symconf93
