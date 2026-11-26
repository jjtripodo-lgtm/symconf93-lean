module
public import Symconf93.Incidence
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-! Pure exact determinant parity, independent from counting leave cycles
or any rational Hasse invariant. -/
namespace Symconf93
open Matrix
open scoped Matrix

section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem integer_gram_determinant_valuations_even (A : Matrix n n ℤ) (p : ℕ) :
    ((A*Aᵀ).det.natAbs.factorization p)%2=0 := by
  rw [Matrix.det_mul,Matrix.det_transpose,Int.natAbs_mul]
  by_cases h : A.det.natAbs=0
  · rw [h,mul_zero,Nat.factorization_zero,Finsupp.zero_apply]
    rfl
  · rw [Nat.factorization_mul h h,Finsupp.add_apply]
    omega

theorem no_integral_gram_of_odd_val (G : Matrix n n ℤ) (p : ℕ)
    (h : (G.det.natAbs.factorization p)%2=1) :
    ¬∃ A : Matrix n n ℤ,G=A*Aᵀ := by
  rintro ⟨A,rfl⟩
  rw [integer_gram_determinant_valuations_even] at h
  omega

end

end Symconf93

#print axioms Symconf93.no_integral_gram_of_odd_val
