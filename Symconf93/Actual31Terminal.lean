module
public import Symconf93.DegreeFiveEndgame31

@[expose] public section

/-! End of the original physical length-31 leave branch. The full order-93
terminal now has exactly the independent coverage and arithmetic premises. -/
namespace Symconf93

theorem no_original_incidence93_with_two_31cube_leaves {A : Int93}
    (h : Incidence93 A)
    (R : OrderedCycles (rowLeave A) P31)
    (C : OrderedCycles (colLeave A) P31) : False :=
  no_two_bank31 (actual_31cubed_to_two_bank h R C)

theorem no_unrestricted_incidence93_of_coverage_and_arithmetic
    (hC : Coverage93) (hA : Arithmetic93) : ¬∃ A : Int93, Incidence93 A :=
  no_unrestricted_incidence93_of_certified_gates hC hA no_two_bank31

end Symconf93

#print axioms Symconf93.no_original_incidence93_with_two_31cube_leaves
#print axioms Symconf93.no_unrestricted_incidence93_of_coverage_and_arithmetic
