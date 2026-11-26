module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w02_03 : List LocalWitness31 := []
private theorem c02_03 : CellCovers31 2 3 := by
  have H : (w02_03.all (validWitness31 proto5) && doubleCoverage31 w02_03 2 3)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_04 : List LocalWitness31 := []
private theorem c02_04 : CellCovers31 2 4 := by
  have H : (w02_04.all (validWitness31 proto5) && doubleCoverage31 w02_04 2 4)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_05 : List LocalWitness31 := [⟨33317,24,false,0⟩,⟨34853,28,false,0⟩,⟨69669,57,false,0⟩,⟨131621,50,false,0⟩,⟨139301,82,false,0⟩,⟨1052709,42,false,0⟩,⟨1064997,86,false,0⟩,⟨4227109,72,false,0⟩,⟨8389157,6,false,0⟩,⟨8390693,1,false,0⟩,⟨8454181,71,false,0⟩,⟨8519717,74,false,0⟩,⟨16842789,55,false,0⟩,⟨17825829,38,false,0⟩,⟨33554981,19,false,0⟩,⟨33558565,0,false,0⟩,⟨35651621,21,false,0⟩,⟨134221861,20,false,0⟩,⟨134225957,7,false,0⟩,⟨134250533,31,false,0⟩,⟨134348837,51,false,0⟩,⟨135266341,25,false,0⟩]
private theorem c02_05 : CellCovers31 2 5 := by
  have H : (w02_05.all (validWitness31 proto5) && doubleCoverage31 w02_05 2 5)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_06 : List LocalWitness31 := [⟨16965,3,false,0⟩,⟨18501,4,false,0⟩,⟨73797,67,false,0⟩,⟨131653,48,false,0⟩,⟨264261,39,false,0⟩,⟨524869,10,false,0⟩,⟨526405,13,false,0⟩,⟨2105413,43,false,0⟩,⟨4718661,85,false,0⟩,⟨8390725,5,false,0⟩,⟨8650821,75,false,0⟩,⟨16793669,11,false,0⟩,⟨16842821,63,false,0⟩,⟨18874437,32,false,0⟩,⟨67371077,37,false,0⟩,⟨75497541,2,false,0⟩,⟨268443717,25,true,2⟩,⟨268501061,51,true,2⟩,⟨268697669,31,true,2⟩,⟨269484101,7,true,2⟩,⟨270532677,20,true,2⟩]
private theorem c02_06 : CellCovers31 2 6 := by
  have H : (w02_06.all (validWitness31 proto5) && doubleCoverage31 w02_06 2 6)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_07 : List LocalWitness31 := [⟨66693,47,false,0⟩,⟨73861,65,false,0⟩,⟨133253,49,false,0⟩,⟨139397,68,false,0⟩,⟨2105477,15,false,0⟩,⟨2130053,77,false,0⟩,⟨2359429,89,false,0⟩,⟨4195461,22,false,0⟩,⟨8390789,23,false,0⟩,⟨33556613,8,false,0⟩,⟨35651717,9,false,0⟩,⟨37748869,27,false,0⟩,⟨134218885,2,true,2⟩,⟨134250629,37,true,2⟩]
private theorem c02_07 : CellCovers31 2 7 := by
  have H : (w02_07.all (validWitness31 proto5) && doubleCoverage31 w02_07 2 7)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_08 : List LocalWitness31 := [⟨35077,26,false,0⟩,⟨37125,30,false,0⟩,⟨135429,52,false,0⟩,⟨139525,66,false,0⟩,⟨264453,29,false,0⟩,⟨557317,84,false,0⟩,⟨1179909,88,false,0⟩,⟨2228485,81,false,0⟩,⟨4456709,73,false,0⟩,⟨17301765,56,false,0⟩,⟨17826053,41,false,0⟩,⟨18874629,35,false,0⟩,⟨67111173,27,true,2⟩,⟨67113221,9,true,2⟩,⟨71303429,8,true,2⟩,⟨268439813,21,true,2⟩,⟨270532869,0,true,2⟩,⟨285212933,19,true,2⟩]
private theorem c02_08 : CellCovers31 2 8 := by
  have H : (w02_08.all (validWitness31 proto5) && doubleCoverage31 w02_08 2 8)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_09 : List LocalWitness31 := [⟨135685,53,false,0⟩,⟨532997,16,false,0⟩,⟨557573,78,false,0⟩,⟨33559045,35,true,2⟩,⟨33563141,41,true,2⟩,⟨33571333,56,true,2⟩,⟨134222341,32,true,2⟩,⟨134349317,63,true,2⟩,⟨134742533,11,true,2⟩,⟨268444165,38,true,2⟩,⟨268567045,55,true,2⟩]
private theorem c02_09 : CellCovers31 2 9 := by
  have H : (w02_09.all (validWitness31 proto5) && doubleCoverage31 w02_09 2 9)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_10 : List LocalWitness31 := [⟨140293,70,false,0⟩,⟨533509,18,false,0⟩,⟨558085,79,false,0⟩,⟨4228101,46,false,0⟩,⟨4326405,62,false,0⟩,⟨71304197,23,true,2⟩,⟨134251525,75,true,2⟩,⟨138413061,5,true,2⟩,⟨268502021,74,true,2⟩,⟨268567557,71,true,2⟩,⟨272630789,1,true,2⟩,⟨285213701,6,true,2⟩]
private theorem c02_10 : CellCovers31 2 10 := by
  have H : (w02_10.all (validWitness31 proto5) && doubleCoverage31 w02_10 2 10)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_11 : List LocalWitness31 := [⟨280581,87,false,0⟩,⟨8456197,62,true,2⟩,⟨8652805,46,true,2⟩,⟨33589253,73,true,2⟩,⟨75499525,22,true,2⟩,⟨134236165,85,true,2⟩,⟨268699653,72,true,2⟩]
private theorem c02_11 : CellCovers31 2 11 := by
  have H : (w02_11.all (validWitness31 proto5) && doubleCoverage31 w02_11 2 11)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_12 : List LocalWitness31 := [⟨1183749,90,false,0⟩,⟨33624069,81,true,2⟩,⟨67145733,89,true,2⟩,⟨67375109,77,true,2⟩,⟨68161541,15,true,2⟩,⟨135270405,43,true,2⟩]
private theorem c02_12 : CellCovers31 2 12 := by
  have H : (w02_12.all (validWitness31 proto5) && doubleCoverage31 w02_12 2 12)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_13 : List LocalWitness31 := [⟨2170885,90,true,2⟩,⟨33628165,88,true,2⟩,⟨268967941,86,true,2⟩,⟨270540805,42,true,2⟩]
private theorem c02_13 : CellCovers31 2 13 := by
  have H : (w02_13.all (validWitness31 proto5) && doubleCoverage31 w02_13 2 13)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_14 : List LocalWitness31 := [⟨8667141,79,true,2⟩,⟨9453573,18,true,2⟩,⟨17055749,78,true,2⟩,⟨17842181,16,true,2⟩,⟨33832965,84,true,2⟩,⟨138428421,13,true,2⟩,⟨151011333,10,true,2⟩]
private theorem c02_14 : CellCovers31 2 14 := by
  have H : (w02_14.all (validWitness31 proto5) && doubleCoverage31 w02_14 2 14)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_15 : List LocalWitness31 := [⟨4751365,87,true,2⟩,⟨37781509,29,true,2⟩,⟨138444805,39,true,2⟩]
private theorem c02_15 : CellCovers31 2 15 := by
  have H : (w02_15.all (validWitness31 proto5) && doubleCoverage31 w02_15 2 15)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_16 : List LocalWitness31 := [⟨9502725,70,true,2⟩,⟨18939909,53,true,2⟩,⟨34668549,66,true,2⟩,⟨35717125,52,true,2⟩,⟨68222981,68,true,2⟩,⟨71368709,49,true,2⟩,⟨151060485,48,true,2⟩,⟨269549573,82,true,2⟩,⟨285278213,50,true,2⟩]
private theorem c02_16 : CellCovers31 2 16 := by
  have H : (w02_16.all (validWitness31 proto5) && doubleCoverage31 w02_16 2 16)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_17 : List LocalWitness31 := [⟨68288517,65,true,2⟩,⟨75628549,47,true,2⟩,⟨135397381,67,true,2⟩,⟨270663685,57,true,2⟩]
private theorem c02_17 : CellCovers31 2 17 := by
  have H : (w02_17.all (validWitness31 proto5) && doubleCoverage31 w02_17 2 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_18 : List LocalWitness31 := [⟨35913733,30,true,2⟩,⟨38010885,26,true,2⟩,⟨272891909,28,true,2⟩,⟨285474821,24,true,2⟩]
private theorem c02_18 : CellCovers31 2 18 := by
  have H : (w02_18.all (validWitness31 proto5) && doubleCoverage31 w02_18 2 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_19 : List LocalWitness31 := [⟨138936325,4,true,2⟩,⟨151519237,3,true,2⟩]
private theorem c02_19 : CellCovers31 2 19 := by
  have H : (w02_19.all (validWitness31 proto5) && doubleCoverage31 w02_19 2 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_20 : List LocalWitness31 := []
private theorem c02_20 : CellCovers31 2 20 := by
  have H : (w02_20.all (validWitness31 proto5) && doubleCoverage31 w02_20 2 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_21 : List LocalWitness31 := []
private theorem c02_21 : CellCovers31 2 21 := by
  have H : (w02_21.all (validWitness31 proto5) && doubleCoverage31 w02_21 2 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_22 : List LocalWitness31 := []
private theorem c02_22 : CellCovers31 2 22 := by
  have H : (w02_22.all (validWitness31 proto5) && doubleCoverage31 w02_22 2 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_23 : List LocalWitness31 := []
private theorem c02_23 : CellCovers31 2 23 := by
  have H : (w02_23.all (validWitness31 proto5) && doubleCoverage31 w02_23 2 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_24 : List LocalWitness31 := []
private theorem c02_24 : CellCovers31 2 24 := by
  have H : (w02_24.all (validWitness31 proto5) && doubleCoverage31 w02_24 2 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_25 : List LocalWitness31 := []
private theorem c02_25 : CellCovers31 2 25 := by
  have H : (w02_25.all (validWitness31 proto5) && doubleCoverage31 w02_25 2 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_26 : List LocalWitness31 := []
private theorem c02_26 : CellCovers31 2 26 := by
  have H : (w02_26.all (validWitness31 proto5) && doubleCoverage31 w02_26 2 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_27 : List LocalWitness31 := []
private theorem c02_27 : CellCovers31 2 27 := by
  have H : (w02_27.all (validWitness31 proto5) && doubleCoverage31 w02_27 2 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_28 : List LocalWitness31 := []
private theorem c02_28 : CellCovers31 2 28 := by
  have H : (w02_28.all (validWitness31 proto5) && doubleCoverage31 w02_28 2 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_29 : List LocalWitness31 := []
private theorem c02_29 : CellCovers31 2 29 := by
  have H : (w02_29.all (validWitness31 proto5) && doubleCoverage31 w02_29 2 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w02_30 : List LocalWitness31 := []
private theorem c02_30 : CellCovers31 2 30 := by
  have H : (w02_30.all (validWitness31 proto5) && doubleCoverage31 w02_30 2 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row02 (v : Fin 31) (h : 2<v.val) : CellCovers31 2 v.val := by
  fin_cases v
  · change 2<0 at h; omega
  · change 2<1 at h; omega
  · change 2<2 at h; omega
  · exact c02_03
  · exact c02_04
  · exact c02_05
  · exact c02_06
  · exact c02_07
  · exact c02_08
  · exact c02_09
  · exact c02_10
  · exact c02_11
  · exact c02_12
  · exact c02_13
  · exact c02_14
  · exact c02_15
  · exact c02_16
  · exact c02_17
  · exact c02_18
  · exact c02_19
  · exact c02_20
  · exact c02_21
  · exact c02_22
  · exact c02_23
  · exact c02_24
  · exact c02_25
  · exact c02_26
  · exact c02_27
  · exact c02_28
  · exact c02_29
  · exact c02_30

end Symconf93
