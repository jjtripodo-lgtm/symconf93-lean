module
public import Symconf93.ExactCoverageParallel93
public import Symconf93.OriginalModularJoin93

@[expose] public section

/-! Install this typed wrapper only once exact_original_coverage93 is
actually compiled on the same original Terminal93 source. -/
namespace Symconf93

theorem no_unrestricted_incidence93_of_literal_modular_rosters
    (h49 : Mod49RosterExclusions93) (h625 : Mod625RosterExclusions93) :
    ¬∃ A : Int93, Incidence93 A :=
  no_unrestricted_incidence93_of_coverage_and_literal_modular_rosters
    exact_original_coverage93 h49 h625

end Symconf93

#print axioms Symconf93.no_unrestricted_incidence93_of_literal_modular_rosters
