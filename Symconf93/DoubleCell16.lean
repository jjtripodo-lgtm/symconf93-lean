module
public import Symconf93.DoubleAnchor31

@[expose] public section

namespace Symconf93
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def w16_17 : List LocalWitness31 := []
private theorem c16_17 : CellCovers31 16 17 := by
  have H : (w16_17.all (validWitness31 proto5) && doubleCoverage31 w16_17 16 17)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_18 : List LocalWitness31 := [⟨35979265,24,false,16⟩,⟨136642561,28,false,16⟩,⟨151322625,26,false,16⟩,⟨285540353,30,false,16⟩]
private theorem c16_18 : CellCovers31 16 18 := by
  have H : (w16_18.all (validWitness31 proto5) && doubleCoverage31 w16_18 16 18)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_19 : List LocalWitness31 := [⟨136904705,21,true,21⟩,⟨545849345,30,true,0⟩]
private theorem c16_19 : CellCovers31 16 19 := by
  have H : (w16_19.all (validWitness31 proto5) && doubleCoverage31 w16_19 16 19)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_20 : List LocalWitness31 := [⟨43057153,19,true,25⟩,⟨336658433,21,false,26⟩,⟨546373633,26,true,0⟩,⟨605093889,28,true,0⟩]
private theorem c16_20 : CellCovers31 16 20 := by
  have H : (w16_20.all (validWitness31 proto5) && doubleCoverage31 w16_20 16 20)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_21 : List LocalWitness31 := []
private theorem c16_21 : CellCovers31 16 21 := by
  have H : (w16_21.all (validWitness31 proto5) && doubleCoverage31 w16_21 16 21)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_22 : List LocalWitness31 := [⟨155254785,19,false,22⟩,⟨608239617,24,true,0⟩]
private theorem c16_22 : CellCovers31 16 22 := by
  have H : (w16_22.all (validWitness31 proto5) && doubleCoverage31 w16_22 16 22)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_23 : List LocalWitness31 := []
private theorem c16_23 : CellCovers31 16 23 := by
  have H : (w16_23.all (validWitness31 proto5) && doubleCoverage31 w16_23 16 23)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_24 : List LocalWitness31 := []
private theorem c16_24 : CellCovers31 16 24 := by
  have H : (w16_24.all (validWitness31 proto5) && doubleCoverage31 w16_24 16 24)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_25 : List LocalWitness31 := []
private theorem c16_25 : CellCovers31 16 25 := by
  have H : (w16_25.all (validWitness31 proto5) && doubleCoverage31 w16_25 16 25)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_26 : List LocalWitness31 := []
private theorem c16_26 : CellCovers31 16 26 := by
  have H : (w16_26.all (validWitness31 proto5) && doubleCoverage31 w16_26 16 26)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_27 : List LocalWitness31 := []
private theorem c16_27 : CellCovers31 16 27 := by
  have H : (w16_27.all (validWitness31 proto5) && doubleCoverage31 w16_27 16 27)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_28 : List LocalWitness31 := []
private theorem c16_28 : CellCovers31 16 28 := by
  have H : (w16_28.all (validWitness31 proto5) && doubleCoverage31 w16_28 16 28)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_29 : List LocalWitness31 := []
private theorem c16_29 : CellCovers31 16 29 := by
  have H : (w16_29.all (validWitness31 proto5) && doubleCoverage31 w16_29 16 29)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

private def w16_30 : List LocalWitness31 := []
private theorem c16_30 : CellCovers31 16 30 := by
  have H : (w16_30.all (validWitness31 proto5) && doubleCoverage31 w16_30 16 30)=true := by decide +kernel
  simp only [Bool.and_eq_true] at H
  exact double_coverage_sound31 H.1 H.2

theorem double_cell_row16 (v : Fin 31) (h : 16<v.val) : CellCovers31 16 v.val := by
  fin_cases v
  · change 16<0 at h; omega
  · change 16<1 at h; omega
  · change 16<2 at h; omega
  · change 16<3 at h; omega
  · change 16<4 at h; omega
  · change 16<5 at h; omega
  · change 16<6 at h; omega
  · change 16<7 at h; omega
  · change 16<8 at h; omega
  · change 16<9 at h; omega
  · change 16<10 at h; omega
  · change 16<11 at h; omega
  · change 16<12 at h; omega
  · change 16<13 at h; omega
  · change 16<14 at h; omega
  · change 16<15 at h; omega
  · change 16<16 at h; omega
  · exact c16_17
  · exact c16_18
  · exact c16_19
  · exact c16_20
  · exact c16_21
  · exact c16_22
  · exact c16_23
  · exact c16_24
  · exact c16_25
  · exact c16_26
  · exact c16_27
  · exact c16_28
  · exact c16_29
  · exact c16_30

end Symconf93
