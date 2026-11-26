module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Nonexistence of a symmetric configuration 93_10
An incidence matrix on 93 points and 93 lines has binary entries, every
row and column sum is 10, and two distinct rows share at most one incidence.
There is no such matrix. No cyclicity or arithmetic premise is imposed.
The deliberate missing proof is the independent statement for comparison.
-/

@[expose] public section
open scoped BigOperators
namespace PalomarSymconf

theorem no_configuration_93_10 :
    ¬ ∃ A : Matrix (Fin 93) (Fin 93) ℤ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i, (∑ j, A i j) = 10) ∧
      (∀ j, (∑ i, A i j) = 10) ∧
      (∀ i i', i ≠ i' → (∑ j, A i j * A i' j) ≤ 1) := by
  sorry

end PalomarSymconf
