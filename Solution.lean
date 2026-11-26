module

public import Symconf93.OriginalIncidence93Complete

/-! Transfer to the original unrestricted binary-incidence theorem. -/

@[expose] public section
open scoped BigOperators
namespace PalomarSymconf

theorem no_configuration_93_10 :
    ¬ ∃ A : Matrix (Fin 93) (Fin 93) ℤ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i, (∑ j, A i j) = 10) ∧
      (∀ j, (∑ i, A i j) = 10) ∧
      (∀ i i', i ≠ i' → (∑ j, A i j * A i' j) ≤ 1) := by
  rintro ⟨A, hb, hr, hc, ho⟩
  exact Symconf93.no_unrestricted_incidence93 ⟨A, ⟨hb, hr, hc, ho⟩⟩

end PalomarSymconf
