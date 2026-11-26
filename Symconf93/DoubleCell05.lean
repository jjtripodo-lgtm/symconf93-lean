module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w05_06 : List LocalWitness31 := []
private theorem c05_06 : CellCovers31 5 6 := by
  have H : (w05_06.all (validWitness31 proto5) && doubleCoverage31 w05_06 5 6)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_07 : List LocalWitness31 := [⟨73889,27,true,7⟩,⟨139425,9,true,7⟩,⟨1179809,89,true,7⟩,⟨8390817,37,false,5⟩,⟨8519841,77,true,7⟩,⟨33685665,15,true,7⟩,⟨35651745,68,true,7⟩,⟨37748897,65,true,7⟩,⟨134226081,8,true,7⟩,⟨134250657,23,true,7⟩,⟨136315041,49,true,7⟩,⟨268437665,2,false,5⟩,⟨268501153,22,true,7⟩,⟨272629921,47,true,7⟩]
private theorem c05_07 : CellCovers31 5 7 := by
  have H : (w05_07.all (validWitness31 proto5) && doubleCoverage31 w05_07 5 7)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_08 : List LocalWitness31 := [⟨20769,3,true,14⟩,⟨164129,53,true,17⟩,⟨557345,58,true,8⟩,⟨2101537,34,false,5⟩,⟨2113825,64,true,8⟩,⟨2228513,80,true,8⟩,⟨2621729,90,false,19⟩,⟨16793889,54,true,8⟩,⟨33558817,12,false,5⟩,⟨35651873,69,true,8⟩,⟨136315169,33,true,8⟩,⟨167772449,4,false,25⟩,⟨536887585,47,false,29⟩,⟨537919777,22,false,29⟩,⟨570425633,2,true,0⟩]
private theorem c05_08 : CellCovers31 5 8 := by
  have H : (w05_08.all (validWitness31 proto5) && doubleCoverage31 w05_08 5 8)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_09 : List LocalWitness31 := [⟨164385,52,true,17⟩,⟨526881,5,true,11⟩,⟨590369,59,true,19⟩,⟨8391201,13,true,11⟩,⟨8393249,14,true,12⟩,⟨10486305,79,false,21⟩,⟨16779809,39,true,11⟩,⟨33559073,40,true,12⟩,⟨41943585,66,false,23⟩,⟨268438049,4,true,11⟩,⟨268468769,33,false,28⟩,⟨536904225,49,false,29⟩,⟨538968609,23,false,29⟩,⟨545260065,8,false,29⟩]
private theorem c05_09 : CellCovers31 5 9 := by
  have H : (w05_09.all (validWitness31 proto5) && doubleCoverage31 w05_09 5 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_10 : List LocalWitness31 := []
private theorem c05_10 : CellCovers31 5 10 := by
  have H : (w05_10.all (validWitness31 proto5) && doubleCoverage31 w05_10 5 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_11 : List LocalWitness31 := [⟨16795681,17,true,14⟩,⟨16812065,44,true,15⟩,⟨134228001,66,true,13⟩,⟨150997025,40,false,24⟩,⟨268470305,69,false,28⟩,⟨285214753,12,true,0⟩,⟨536889377,65,false,29⟩,⟨536905761,68,false,29⟩,⟨537397281,15,false,29⟩]
private theorem c05_11 : CellCovers31 5 11 := by
  have H : (w05_11.all (validWitness31 proto5) && doubleCoverage31 w05_11 5 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_12 : List LocalWitness31 := [⟨1069089,56,false,12⟩,⟨4263969,60,false,12⟩,⟨5247009,62,true,22⟩,⟨10489889,46,false,21⟩,⟨35655713,44,false,21⟩,⟨37752865,17,false,22⟩,⟨167776289,39,false,25⟩,⟨272633889,54,false,28⟩]
private theorem c05_12 : CellCovers31 5 12 := by
  have H : (w05_12.all (validWitness31 proto5) && doubleCoverage31 w05_12 5 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_13 : List LocalWitness31 := [⟨565281,75,false,13⟩,⟨1187873,83,true,20⟩,⟨16818209,46,true,15⟩,⟨134258721,79,true,15⟩,⟨151003169,14,false,24⟩,⟨167780385,13,false,25⟩,⟨537403425,77,false,29⟩,⟨570433569,37,true,0⟩]
private theorem c05_13 : CellCovers31 5 13 := by
  have H : (w05_13.all (validWitness31 proto5) && doubleCoverage31 w05_13 5 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_14 : List LocalWitness31 := [⟨16859169,62,false,14⟩,⟨17842209,60,true,24⟩]
private theorem c05_14 : CellCovers31 5 14 := by
  have H : (w05_14.all (validWitness31 proto5) && doubleCoverage31 w05_14 5 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_15 : List LocalWitness31 := [⟨268599329,90,true,17⟩,⟨268992545,80,false,28⟩,⟨272662561,64,false,28⟩,⟨285245473,34,true,0⟩]
private theorem c05_15 : CellCovers31 5 15 := by
  have H : (w05_15.all (validWitness31 proto5) && doubleCoverage31 w05_15 5 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_16 : List LocalWitness31 := [⟨8978465,83,false,16⟩,⟨21037089,56,true,24⟩,⟨537460769,89,false,29⟩]
private theorem c05_16 : CellCovers31 5 16 := by
  have H : (w05_16.all (validWitness31 proto5) && doubleCoverage31 w05_16 5 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_17 : List LocalWitness31 := [⟨10616865,75,true,23⟩,⟨135397409,59,false,17⟩,⟨167903265,5,false,25⟩,⟨270663713,58,false,28⟩]
private theorem c05_17 : CellCovers31 5 17 := by
  have H : (w05_17.all (validWitness31 proto5) && doubleCoverage31 w05_17 5 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_18 : List LocalWitness31 := []
private theorem c05_18 : CellCovers31 5 18 := by
  have H : (w05_18.all (validWitness31 proto5) && doubleCoverage31 w05_18 5 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_19 : List LocalWitness31 := [⟨136839201,52,false,19⟩,⟨271056929,53,false,19⟩,⟨545783841,9,false,29⟩]
private theorem c05_19 : CellCovers31 5 19 := by
  have H : (w05_19.all (validWitness31 proto5) && doubleCoverage31 w05_19 5 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_20 : List LocalWitness31 := [⟨546308129,27,false,29⟩]
private theorem c05_20 : CellCovers31 5 20 := by
  have H : (w05_20.all (validWitness31 proto5) && doubleCoverage31 w05_20 5 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_21 : List LocalWitness31 := []
private theorem c05_21 : CellCovers31 5 21 := by
  have H : (w05_21.all (validWitness31 proto5) && doubleCoverage31 w05_21 5 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_22 : List LocalWitness31 := [⟨289407009,3,false,22⟩]
private theorem c05_22 : CellCovers31 5 22 := by
  have H : (w05_22.all (validWitness31 proto5) && doubleCoverage31 w05_22 5 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_23 : List LocalWitness31 := []
private theorem c05_23 : CellCovers31 5 23 := by
  have H : (w05_23.all (validWitness31 proto5) && doubleCoverage31 w05_23 5 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_24 : List LocalWitness31 := []
private theorem c05_24 : CellCovers31 5 24 := by
  have H : (w05_24.all (validWitness31 proto5) && doubleCoverage31 w05_24 5 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_25 : List LocalWitness31 := []
private theorem c05_25 : CellCovers31 5 25 := by
  have H : (w05_25.all (validWitness31 proto5) && doubleCoverage31 w05_25 5 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_26 : List LocalWitness31 := []
private theorem c05_26 : CellCovers31 5 26 := by
  have H : (w05_26.all (validWitness31 proto5) && doubleCoverage31 w05_26 5 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_27 : List LocalWitness31 := []
private theorem c05_27 : CellCovers31 5 27 := by
  have H : (w05_27.all (validWitness31 proto5) && doubleCoverage31 w05_27 5 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_28 : List LocalWitness31 := []
private theorem c05_28 : CellCovers31 5 28 := by
  have H : (w05_28.all (validWitness31 proto5) && doubleCoverage31 w05_28 5 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_29 : List LocalWitness31 := []
private theorem c05_29 : CellCovers31 5 29 := by
  have H : (w05_29.all (validWitness31 proto5) && doubleCoverage31 w05_29 5 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w05_30 : List LocalWitness31 := []
private theorem c05_30 : CellCovers31 5 30 := by
  have H : (w05_30.all (validWitness31 proto5) && doubleCoverage31 w05_30 5 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row05 (v : Fin 31) (h : 5<v.val) : CellCovers31 5 v.val := by
  fin_cases v
  · change 5<0 at h; omega
  · change 5<1 at h; omega
  · change 5<2 at h; omega
  · change 5<3 at h; omega
  · change 5<4 at h; omega
  · change 5<5 at h; omega
  · exact c05_06
  · exact c05_07
  · exact c05_08
  · exact c05_09
  · exact c05_10
  · exact c05_11
  · exact c05_12
  · exact c05_13
  · exact c05_14
  · exact c05_15
  · exact c05_16
  · exact c05_17
  · exact c05_18
  · exact c05_19
  · exact c05_20
  · exact c05_21
  · exact c05_22
  · exact c05_23
  · exact c05_24
  · exact c05_25
  · exact c05_26
  · exact c05_27
  · exact c05_28
  · exact c05_29
  · exact c05_30

end Symconf93
