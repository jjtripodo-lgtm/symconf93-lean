module
public import Symconf93.Terminal93

@[expose] public section

/-! Source-authenticated physical 25-profile roster in descending order. -/
namespace Symconf93

namespace ModCount49

def profile (i : Fin 2) : List ℕ :=
  (#[
  [5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [15, 15, 15, 15, 15, 3, 3, 3, 3, 3, 3]
  ] : Array (List ℕ))[i.val]!

theorem roster_mem : ∀ i : Fin 2, profile i ∈ profiles37 := by decide +kernel
theorem roster_nonresidual : ∀ i : Fin 2, profile i ≠ P31 ∧ profile i ≠ Mixed37 := by decide +kernel

end ModCount49
#print axioms ModCount49.roster_mem
#print axioms ModCount49.roster_nonresidual

namespace ModCount625

def profile (i : Fin 23) : List ℕ :=
  (#[
  [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [9, 9, 9, 9, 9, 9, 9, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3],
  [9, 9, 9, 9, 9, 9, 9, 9, 3, 3, 3, 3, 3, 3, 3],
  [12, 12, 12, 12, 12, 12, 3, 3, 3, 3, 3, 3, 3],
  [12, 12, 12, 12, 12, 6, 6, 6, 3, 3, 3, 3, 3],
  [9, 9, 9, 9, 9, 9, 9, 9, 9, 3, 3, 3, 3],
  [18, 18, 18, 18, 9, 3, 3, 3, 3],
  [27, 27, 27, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3],
  [12, 12, 12, 12, 12, 12, 6, 6, 3, 3, 3],
  [24, 24, 24, 12, 3, 3, 3],
  [21, 21, 21, 21, 3, 3, 3],
  [15, 15, 15, 15, 15, 5, 5, 5, 3],
  [12, 12, 12, 12, 12, 6, 6, 6, 6, 6, 3],
  [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 3],
  [18, 18, 18, 18, 9, 9, 3],
  [27, 27, 27, 9, 3],
  [15, 15, 15, 15, 15, 15, 3],
  [93]
  ] : Array (List ℕ))[i.val]!

theorem roster_mem : ∀ i : Fin 23, profile i ∈ profiles37 := by decide +kernel
theorem roster_nonresidual : ∀ i : Fin 23, profile i ≠ P31 ∧ profile i ≠ Mixed37 := by decide +kernel

end ModCount625
#print axioms ModCount625.roster_mem
#print axioms ModCount625.roster_nonresidual

theorem source_modular_profiles_nodup :
    (((List.finRange 2).map ModCount49.profile) ++
      ((List.finRange 23).map ModCount625.profile)).Nodup := by decide +kernel

end Symconf93
#print axioms Symconf93.source_modular_profiles_nodup
