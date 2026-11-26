module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w04_05 : List LocalWitness31 := []
private theorem c04_05 : CellCovers31 4 5 := by
  have H : (w04_05.all (validWitness31 proto5) && doubleCoverage31 w04_05 4 5)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_06 : List LocalWitness31 := [⟨18513,2,true,6⟩,⟨66129,20,false,4⟩,⟨73809,32,true,6⟩,⟨131665,7,false,4⟩,⟨294993,85,true,6⟩,⟨524881,31,false,4⟩,⟨526417,37,true,6⟩,⟨540753,75,true,6⟩,⟨2097745,51,false,4⟩,⟨2105425,63,true,6⟩,⟨8396881,11,true,6⟩,⟨16777809,25,false,4⟩,⟨16842833,43,true,6⟩,⟨18874449,67,true,6⟩,⟨67125329,5,true,6⟩,⟨67371089,13,true,6⟩,⟨67633233,39,true,6⟩,⟨75497553,4,true,6⟩,⟨268697681,10,true,6⟩,⟨269484113,48,true,6⟩,⟨276824145,3,true,6⟩]
private theorem c04_06 : CellCovers31 4 6 := by
  have H : (w04_06.all (validWitness31 proto5) && doubleCoverage31 w04_06 4 6)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_07 : List LocalWitness31 := [⟨33425,19,true,9⟩,⟨41105,26,true,15⟩,⟨131729,6,true,9⟩,⟨163985,70,true,17⟩,⟨266385,12,true,7⟩,⟨327825,87,true,18⟩,⟨4198545,34,true,7⟩,⟨8389265,50,true,9⟩,⟨8396945,36,true,7⟩,⟨8519825,76,true,7⟩,⟨8650897,83,true,7⟩,⟨33555089,24,true,9⟩,⟨41943185,30,false,23⟩,⟨67371153,14,true,7⟩,⟨68157585,40,true,7⟩,⟨536875153,3,false,29⟩,⟨536903825,48,false,29⟩,⟨537002129,10,false,29⟩]
private theorem c04_07 : CellCovers31 4 7 := by
  have H : (w04_07.all (validWitness31 proto5) && doubleCoverage31 w04_07 4 7)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_08 : List LocalWitness31 := []
private theorem c04_08 : CellCovers31 4 8 := by
  have H : (w04_08.all (validWitness31 proto5) && doubleCoverage31 w04_08 4 8)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_09 : List LocalWitness31 := [⟨133649,8,true,11⟩,⟨164369,66,true,17⟩,⟨526865,23,true,11⟩,⟨655889,79,true,19⟩,⟨18874897,59,false,21⟩,⟨33557009,49,true,11⟩,⟨33559057,33,true,12⟩,⟨41943569,52,false,23⟩,⟨268468753,40,false,28⟩,⟨268567057,14,false,28⟩,⟨536875537,4,false,29⟩,⟨536936977,39,false,29⟩,⟨537002513,13,false,29⟩,⟨538968593,5,false,29⟩]
private theorem c04_09 : CellCovers31 4 9 := by
  have H : (w04_09.all (validWitness31 proto5) && doubleCoverage31 w04_09 4 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_10 : List LocalWitness31 := [⟨37905,21,false,10⟩,⟨42001,28,true,15⟩,⟨136209,9,false,10⟩,⟨164881,68,true,17⟩,⟨295953,69,true,18⟩,⟨656401,78,true,19⟩,⟨4228113,44,false,0⟩,⟨17302545,60,false,0⟩,⟨20972561,16,false,22⟩,⟨67114001,52,true,12⟩,⟨75498513,33,false,23⟩,⟨83887121,49,false,24⟩,⟨268440593,30,true,12⟩,⟨335545361,24,false,26⟩]
private theorem c04_10 : CellCovers31 4 10 := by
  have H : (w04_10.all (validWitness31 proto5) && doubleCoverage31 w04_10 4 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_11 : List LocalWitness31 := [⟨75793,38,false,11⟩,⟨83985,57,true,16⟩,⟨534545,41,false,11⟩,⟨542737,58,false,11⟩,⟨657425,84,true,19⟩,⟨33564689,16,true,13⟩,⟨33622033,60,true,4⟩,⟨67127313,59,true,14⟩,⟨536889361,67,false,29⟩,⟨537397265,43,false,29⟩,⟨603981841,25,true,0⟩]
private theorem c04_11 : CellCovers31 4 11 := by
  have H : (w04_11.all (validWitness31 proto5) && doubleCoverage31 w04_11 4 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_12 : List LocalWitness31 := [⟨167953,82,true,17⟩,⟨2134033,61,false,12⟩,⟨4231185,45,false,12⟩,⟨268570641,83,false,28⟩,⟨268701713,76,false,28⟩,⟨272633873,36,false,28⟩,⟨335548433,50,false,26⟩,⟨541069329,11,false,29⟩]
private theorem c04_12 : CellCovers31 4 12 := by
  have H : (w04_12.all (validWitness31 proto5) && doubleCoverage31 w04_12 4 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_13 : List LocalWitness31 := [⟨2138129,73,false,13⟩,⟨2170897,80,false,13⟩,⟨2629649,81,true,21⟩,⟨9445393,45,true,23⟩,⟨34611217,44,true,4⟩,⟨276832273,34,false,28⟩]
private theorem c04_13 : CellCovers31 4 13 := by
  have H : (w04_13.all (validWitness31 proto5) && doubleCoverage31 w04_13 4 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_14 : List LocalWitness31 := [⟨4276241,81,false,14⟩,⟨4734993,80,true,22⟩,⟨5259281,73,true,22⟩,⟨9453585,61,true,23⟩,⟨541081617,63,false,29⟩,⟨603996177,51,true,0⟩]
private theorem c04_14 : CellCovers31 4 14 := by
  have H : (w04_14.all (validWitness31 proto5) && doubleCoverage31 w04_14 4 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_15 : List LocalWitness31 := []
private theorem c04_15 : CellCovers31 4 15 := by
  have H : (w04_15.all (validWitness31 proto5) && doubleCoverage31 w04_15 4 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_16 : List LocalWitness31 := [⟨17104913,84,false,16⟩,⟨18939921,58,true,24⟩,⟨21037073,41,true,24⟩,⟨33882129,78,false,16⟩,⟨67436561,79,false,16⟩,⟨83951633,23,false,24⟩,⟨539033617,75,false,29⟩,⟨553713681,37,false,29⟩,⟨604045329,31,true,0⟩]
private theorem c04_16 : CellCovers31 4 16 := by
  have H : (w04_16.all (validWitness31 proto5) && doubleCoverage31 w04_16 4 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_17 : List LocalWitness31 := [⟨34734097,69,false,17⟩,⟨269090833,87,false,17⟩,⟨276955153,12,false,28⟩,⟨538050577,85,false,29⟩]
private theorem c04_17 : CellCovers31 4 17 := by
  have H : (w04_17.all (validWitness31 proto5) && doubleCoverage31 w04_17 4 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_18 : List LocalWitness31 := [⟨9699345,82,false,18⟩,⟨34865169,68,false,18⟩,⟨42205201,9,true,25⟩,⟨68419601,66,false,18⟩,⟨84148241,8,false,24⟩,⟨269746193,70,false,18⟩,⟨335806481,6,false,26⟩,⟨604241937,7,true,0⟩]
private theorem c04_18 : CellCovers31 4 18 := by
  have H : (w04_18.all (validWitness31 proto5) && doubleCoverage31 w04_18 4 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_19 : List LocalWitness31 := [⟨19398673,57,false,19⟩,⟨21495825,38,true,24⟩,⟨541589521,32,false,29⟩,⟨604504081,20,true,0⟩]
private theorem c04_19 : CellCovers31 4 19 := by
  have H : (w04_19.all (validWitness31 proto5) && doubleCoverage31 w04_19 4 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_20 : List LocalWitness31 := [⟨38797329,28,false,20⟩,⟨42991633,21,true,25⟩,⟨273678353,26,false,20⟩,⟨336592913,19,false,26⟩]
private theorem c04_20 : CellCovers31 4 20 := by
  have H : (w04_20.all (validWitness31 proto5) && doubleCoverage31 w04_20 4 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_21 : List LocalWitness31 := [⟨555745297,2,false,29⟩]
private theorem c04_21 : CellCovers31 4 21 := by
  have H : (w04_21.all (validWitness31 proto5) && doubleCoverage31 w04_21 4 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_22 : List LocalWitness31 := []
private theorem c04_22 : CellCovers31 4 22 := by
  have H : (w04_22.all (validWitness31 proto5) && doubleCoverage31 w04_22 4 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_23 : List LocalWitness31 := []
private theorem c04_23 : CellCovers31 4 23 := by
  have H : (w04_23.all (validWitness31 proto5) && doubleCoverage31 w04_23 4 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_24 : List LocalWitness31 := []
private theorem c04_24 : CellCovers31 4 24 := by
  have H : (w04_24.all (validWitness31 proto5) && doubleCoverage31 w04_24 4 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_25 : List LocalWitness31 := []
private theorem c04_25 : CellCovers31 4 25 := by
  have H : (w04_25.all (validWitness31 proto5) && doubleCoverage31 w04_25 4 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_26 : List LocalWitness31 := []
private theorem c04_26 : CellCovers31 4 26 := by
  have H : (w04_26.all (validWitness31 proto5) && doubleCoverage31 w04_26 4 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_27 : List LocalWitness31 := []
private theorem c04_27 : CellCovers31 4 27 := by
  have H : (w04_27.all (validWitness31 proto5) && doubleCoverage31 w04_27 4 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_28 : List LocalWitness31 := []
private theorem c04_28 : CellCovers31 4 28 := by
  have H : (w04_28.all (validWitness31 proto5) && doubleCoverage31 w04_28 4 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_29 : List LocalWitness31 := []
private theorem c04_29 : CellCovers31 4 29 := by
  have H : (w04_29.all (validWitness31 proto5) && doubleCoverage31 w04_29 4 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w04_30 : List LocalWitness31 := []
private theorem c04_30 : CellCovers31 4 30 := by
  have H : (w04_30.all (validWitness31 proto5) && doubleCoverage31 w04_30 4 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row04 (v : Fin 31) (h : 4<v.val) : CellCovers31 4 v.val := by
  fin_cases v
  · change 4<0 at h; omega
  · change 4<1 at h; omega
  · change 4<2 at h; omega
  · change 4<3 at h; omega
  · change 4<4 at h; omega
  · exact c04_05
  · exact c04_06
  · exact c04_07
  · exact c04_08
  · exact c04_09
  · exact c04_10
  · exact c04_11
  · exact c04_12
  · exact c04_13
  · exact c04_14
  · exact c04_15
  · exact c04_16
  · exact c04_17
  · exact c04_18
  · exact c04_19
  · exact c04_20
  · exact c04_21
  · exact c04_22
  · exact c04_23
  · exact c04_24
  · exact c04_25
  · exact c04_26
  · exact c04_27
  · exact c04_28
  · exact c04_29
  · exact c04_30

end Symconf93
