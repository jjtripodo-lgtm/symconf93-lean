module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w03_04 : List LocalWitness31 := []
private theorem c03_04 : CellCovers31 3 4 := by
  have H : (w03_04.all (validWitness31 proto5) && doubleCoverage31 w03_04 3 4)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_05 : List LocalWitness31 := [⟨34857,21,true,5⟩,⟨66089,25,true,5⟩,⟨69673,38,true,5⟩,⟨524841,51,true,5⟩,⟨532521,74,true,5⟩,⟨1052713,55,true,5⟩,⟨1056809,71,true,5⟩,⟨2097705,31,true,5⟩,⟨2113577,72,true,5⟩,⟨4259881,86,true,5⟩,⟨8389161,7,true,5⟩,⟨8912937,82,true,5⟩,⟨16777769,20,true,5⟩,⟨16779305,0,true,5⟩,⟨16842793,42,true,5⟩,⟨17825833,57,true,5⟩,⟨33562665,1,true,5⟩,⟨35651625,28,true,5⟩,⟨134219817,19,true,5⟩,⟨134225961,6,true,5⟩,⟨134742057,50,true,5⟩,⟨136314921,24,true,5⟩]
private theorem c03_05 : CellCovers31 3 5 := by
  have H : (w03_05.all (validWitness31 proto5) && doubleCoverage31 w03_05 3 5)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_06 : List LocalWitness31 := []
private theorem c03_06 : CellCovers31 3 6 := by
  have H : (w03_06.all (validWitness31 proto5) && doubleCoverage31 w03_06 3 6)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_07 : List LocalWitness31 := [⟨41097,30,true,15⟩,⟨266377,40,false,0⟩,⟨1052809,14,false,0⟩,⟨1081481,83,false,0⟩,⟨2097801,10,true,9⟩,⟨2130057,76,false,0⟩,⟨5243017,87,false,20⟩,⟨8389257,48,true,9⟩,⟨10485897,70,false,21⟩,⟨33587337,36,false,0⟩,⟨41943177,26,false,23⟩,⟨67109513,3,true,9⟩,⟨67174537,34,false,0⟩,⟨68157577,12,false,0⟩,⟨536879241,24,false,29⟩,⟨536903817,50,false,29⟩,⟨538968201,6,false,29⟩,⟨545259657,19,false,29⟩]
private theorem c03_07 : CellCovers31 3 7 := by
  have H : (w03_07.all (validWitness31 proto5) && doubleCoverage31 w03_07 3 7)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_08 : List LocalWitness31 := [⟨17673,2,false,8⟩,⟨20745,4,true,14⟩,⟨266505,33,false,0⟩,⟨278793,69,false,0⟩,⟨525577,22,true,10⟩,⟨1310985,90,true,20⟩,⟨4456713,80,false,0⟩,⟨17826057,58,false,0⟩,⟨20971785,53,false,22⟩,⟨33555721,47,true,10⟩,⟨33587465,54,false,0⟩,⟨33816841,64,false,0⟩,⟨134234377,12,true,3⟩,⟨134480137,34,true,3⟩,⟨167772425,3,false,25⟩]
private theorem c03_08 : CellCovers31 3 8 := by
  have H : (w03_08.all (validWitness31 proto5) && doubleCoverage31 w03_08 3 8)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_09 : List LocalWitness31 := [⟨68105,27,false,9⟩,⟨82441,65,true,16⟩,⟨2114057,17,false,0⟩,⟨8913417,61,false,0⟩,⟨10486281,18,false,21⟩,⟨16779785,29,true,11⟩,⟨67174921,64,true,3⟩,⟨67633673,54,true,3⟩,⟨83886601,47,false,24⟩,⟨134220297,26,true,11⟩,⟨134742537,36,true,3⟩,⟨536879625,28,false,29⟩,⟨538968585,1,false,29⟩]
private theorem c03_09 : CellCovers31 3 9 := by
  have H : (w03_09.all (validWitness31 proto5) && doubleCoverage31 w03_09 3 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_10 : List LocalWitness31 := [⟨70665,32,false,10⟩,⟨82953,67,true,16⟩,⟨267273,35,false,10⟩,⟨541705,59,false,0⟩,⟨8913929,45,false,0⟩,⟨41944073,29,false,23⟩,⟨67113993,53,true,12⟩,⟨67126281,58,true,3⟩,⟨536888329,57,false,29⟩,⟨537134089,42,false,29⟩,⟨545260553,0,false,29⟩,⟨570426377,20,false,29⟩]
private theorem c03_10 : CellCovers31 3 10 := by
  have H : (w03_10.all (validWitness31 proto5) && doubleCoverage31 w03_10 3 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_11 : List LocalWitness31 := [⟨16812041,45,true,3⟩,⟨33564681,18,true,13⟩,⟨33589257,61,true,3⟩,⟨134227977,70,true,13⟩,⟨167774217,48,false,25⟩,⟨536905737,82,false,29⟩,⟨570427401,7,false,29⟩]
private theorem c03_11 : CellCovers31 3 11 := by
  have H : (w03_11.all (validWitness31 proto5) && doubleCoverage31 w03_11 3 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_12 : List LocalWitness31 := [⟨282633,85,false,12⟩,⟨1314825,88,true,20⟩,⟨67178505,80,true,3⟩,⟨134238217,87,true,14⟩,⟨537137161,86,false,29⟩]
private theorem c03_12 : CellCovers31 3 12 := by
  have H : (w03_12.all (validWitness31 proto5) && doubleCoverage31 w03_12 3 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_13 : List LocalWitness31 := [⟨1089545,89,false,13⟩,⟨34611209,17,true,3⟩,⟨134750217,76,true,3⟩,⟨167780361,10,false,25⟩,⟨537927689,72,false,29⟩,⟨570433545,31,false,29⟩]
private theorem c03_13 : CellCovers31 3 13 := by
  have H : (w03_13.all (validWitness31 proto5) && doubleCoverage31 w03_13 3 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_14 : List LocalWitness31 := [⟨2637833,89,true,21⟩,⟨4276233,88,false,14⟩,⟨67190793,90,false,14⟩,⟨134758409,83,true,3⟩,⟨138428425,14,true,3⟩,⟨538984457,71,false,29⟩,⟨541081609,55,false,29⟩]
private theorem c03_14 : CellCovers31 3 14 := by
  have H : (w03_14.all (validWitness31 proto5) && doubleCoverage31 w03_14 3 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_15 : List LocalWitness31 := [⟨17858569,59,true,3⟩,⟨83918857,22,false,24⟩,⟨539000841,74,false,29⟩,⟨570458121,51,false,29⟩]
private theorem c03_15 : CellCovers31 3 15 := by
  have H : (w03_15.all (validWitness31 proto5) && doubleCoverage31 w03_15 3 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_16 : List LocalWitness31 := [⟨5308425,85,true,22⟩,⟨21037065,35,true,24⟩,⟨68222985,69,true,3⟩,⟨71368713,33,true,3⟩,⟨138477577,40,true,3⟩]
private theorem c03_16 : CellCovers31 3 16 := by
  have H : (w03_16.all (validWitness31 proto5) && doubleCoverage31 w03_16 3 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_17 : List LocalWitness31 := []
private theorem c03_17 : CellCovers31 3 17 := by
  have H : (w03_17.all (validWitness31 proto5) && doubleCoverage31 w03_17 3 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_18 : List LocalWitness31 := [⟨18087945,67,false,18⟩,⟨21233673,32,true,24⟩,⟨34865161,65,false,18⟩,⟨42205193,27,true,25⟩,⟨541327369,38,false,29⟩,⟨570687497,25,false,29⟩]
private theorem c03_18 : CellCovers31 3 18 := by
  have H : (w03_18.all (validWitness31 proto5) && doubleCoverage31 w03_18 3 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_19 : List LocalWitness31 := [⟨136839177,30,false,19⟩,⟨545783817,21,false,29⟩]
private theorem c03_19 : CellCovers31 3 19 := by
  have H : (w03_19.all (validWitness31 proto5) && doubleCoverage31 w03_19 3 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_20 : List LocalWitness31 := [⟨72351753,4,false,20⟩,⟨84934665,2,true,26⟩]
private theorem c03_20 : CellCovers31 3 20 := by
  have H : (w03_20.all (validWitness31 proto5) && doubleCoverage31 w03_20 3 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_21 : List LocalWitness31 := []
private theorem c03_21 : CellCovers31 3 21 := by
  have H : (w03_21.all (validWitness31 proto5) && doubleCoverage31 w03_21 3 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_22 : List LocalWitness31 := []
private theorem c03_22 : CellCovers31 3 22 := by
  have H : (w03_22.all (validWitness31 proto5) && doubleCoverage31 w03_22 3 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_23 : List LocalWitness31 := []
private theorem c03_23 : CellCovers31 3 23 := by
  have H : (w03_23.all (validWitness31 proto5) && doubleCoverage31 w03_23 3 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_24 : List LocalWitness31 := []
private theorem c03_24 : CellCovers31 3 24 := by
  have H : (w03_24.all (validWitness31 proto5) && doubleCoverage31 w03_24 3 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_25 : List LocalWitness31 := []
private theorem c03_25 : CellCovers31 3 25 := by
  have H : (w03_25.all (validWitness31 proto5) && doubleCoverage31 w03_25 3 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_26 : List LocalWitness31 := []
private theorem c03_26 : CellCovers31 3 26 := by
  have H : (w03_26.all (validWitness31 proto5) && doubleCoverage31 w03_26 3 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_27 : List LocalWitness31 := []
private theorem c03_27 : CellCovers31 3 27 := by
  have H : (w03_27.all (validWitness31 proto5) && doubleCoverage31 w03_27 3 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_28 : List LocalWitness31 := []
private theorem c03_28 : CellCovers31 3 28 := by
  have H : (w03_28.all (validWitness31 proto5) && doubleCoverage31 w03_28 3 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_29 : List LocalWitness31 := []
private theorem c03_29 : CellCovers31 3 29 := by
  have H : (w03_29.all (validWitness31 proto5) && doubleCoverage31 w03_29 3 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w03_30 : List LocalWitness31 := []
private theorem c03_30 : CellCovers31 3 30 := by
  have H : (w03_30.all (validWitness31 proto5) && doubleCoverage31 w03_30 3 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row03 (v : Fin 31) (h : 3<v.val) : CellCovers31 3 v.val := by
  fin_cases v
  · change 3<0 at h; omega
  · change 3<1 at h; omega
  · change 3<2 at h; omega
  · change 3<3 at h; omega
  · exact c03_04
  · exact c03_05
  · exact c03_06
  · exact c03_07
  · exact c03_08
  · exact c03_09
  · exact c03_10
  · exact c03_11
  · exact c03_12
  · exact c03_13
  · exact c03_14
  · exact c03_15
  · exact c03_16
  · exact c03_17
  · exact c03_18
  · exact c03_19
  · exact c03_20
  · exact c03_21
  · exact c03_22
  · exact c03_23
  · exact c03_24
  · exact c03_25
  · exact c03_26
  · exact c03_27
  · exact c03_28
  · exact c03_29
  · exact c03_30

end Symconf93
