module
public import Symconf93.DoubleCell01
public import Symconf93.DoubleCell02
public import Symconf93.DoubleCell03
public import Symconf93.DoubleCell04
public import Symconf93.DoubleCell05
public import Symconf93.DoubleCell06
public import Symconf93.DoubleCell07
public import Symconf93.DoubleCell08
public import Symconf93.DoubleCell09
public import Symconf93.DoubleCell10
public import Symconf93.DoubleCell11
public import Symconf93.DoubleCell12
public import Symconf93.DoubleCell13
public import Symconf93.DoubleCell14
public import Symconf93.DoubleCell15
public import Symconf93.DoubleCell16
public import Symconf93.DoubleCell17
public import Symconf93.DoubleCell18
public import Symconf93.DoubleCell19
public import Symconf93.DoubleCell20
public import Symconf93.DoubleCell21
public import Symconf93.DoubleCell22
public import Symconf93.DoubleCell23
public import Symconf93.DoubleCell24
public import Symconf93.DoubleCell25
public import Symconf93.DoubleCell26
public import Symconf93.DoubleCell27
public import Symconf93.DoubleCell28
public import Symconf93.DoubleCell29

public import Symconf93.JoinedEndgame31

@[expose] public section

namespace Symconf93
theorem local5_all_double_cells31 : ∀ u v : Fin 31, 0<u.val → u.val<v.val → CellCovers31 u.val v.val := by
  intro u v hu hv
  fin_cases u
  · change 0<0 at hu; omega
  · exact double_cell_row01 v hv
  · exact double_cell_row02 v hv
  · exact double_cell_row03 v hv
  · exact double_cell_row04 v hv
  · exact double_cell_row05 v hv
  · exact double_cell_row06 v hv
  · exact double_cell_row07 v hv
  · exact double_cell_row08 v hv
  · exact double_cell_row09 v hv
  · exact double_cell_row10 v hv
  · exact double_cell_row11 v hv
  · exact double_cell_row12 v hv
  · exact double_cell_row13 v hv
  · exact double_cell_row14 v hv
  · exact double_cell_row15 v hv
  · exact double_cell_row16 v hv
  · exact double_cell_row17 v hv
  · exact double_cell_row18 v hv
  · exact double_cell_row19 v hv
  · exact double_cell_row20 v hv
  · exact double_cell_row21 v hv
  · exact double_cell_row22 v hv
  · exact double_cell_row23 v hv
  · exact double_cell_row24 v hv
  · exact double_cell_row25 v hv
  · exact double_cell_row26 v hv
  · exact double_cell_row27 v hv
  · exact double_cell_row28 v hv
  · exact double_cell_row29 v hv
  · change 30<v.val at hv; have ht := v.isLt; omega

theorem local5_complete_coverage31 : ∀ u : Fin 31, 0<u.val → coverage31At proto5 5 u.val=true :=
  local5_coverage_of_double_cells31 local5_all_double_cells31

theorem no_two_bank31 : PhaseEndgame93 := by
  rintro ⟨X⟩
  obtain ⟨Y⟩ := normalize_physical_banks31 X
  exact no_fixed_banks31_of_degree5_coverage local5_complete_coverage31 Y

end Symconf93

#print axioms Symconf93.local5_all_double_cells31
#print axioms Symconf93.local5_complete_coverage31
#print axioms Symconf93.no_two_bank31
