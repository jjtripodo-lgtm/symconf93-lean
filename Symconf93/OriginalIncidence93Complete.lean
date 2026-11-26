module
public import Symconf93.ExactCoverageTerminal93
public import Symconf93.PivotFreeQ49Terminal
public import Symconf93.PivotFreeQ625Terminal

@[expose] public section

namespace Symconf93

/-- Unrestricted original symmetric order-93 configuration nonexistence.
No profile, cycle-length, arithmetic or finite-admission hypothesis remains. -/
theorem no_unrestricted_incidence93 : ¬∃ A : Int93, Incidence93 A :=
  no_unrestricted_incidence93_of_literal_modular_rosters
    AffineFiber49.no_integral_gram49_without_pivots
    AffineFiber625.no_integral_gram625_without_pivots

#print axioms no_unrestricted_incidence93
end Symconf93
