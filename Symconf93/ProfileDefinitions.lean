module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Exact mixed profile exclusions from the first, second and cross
moments. The stronger target does not even need periodicity. -/
namespace Symconf93
open scoped BigOperators

/-- Two weighted moments and exact integer block total conversion. -/
structure ProfileRow {ι : Type*} [Fintype ι] (L : ι → ℕ) (a : ℕ) where
  u : ι → ℕ
  v : ι → ℕ
  block : ∀ j, a*u j=L j*v j
  momentOne : (∑ j,L j*v j)=10*a
  momentTwo : (∑ j,L j*v j*v j)=a*(a+7)

def CrossMoment {ι : Type*} [Fintype ι] {L : ι → ℕ} {a b : ℕ}
    (r : ProfileRow L a) (s : ProfileRow L b) : Prop :=
  (∑ j,L j*r.v j*s.v j)=a*b


def ProfileRow.PeriodBounds {ι : Type*} [Fintype ι] {L : ι → ℕ} {a : ℕ}
    (r : ProfileRow L a) : Prop :=
  ∀ d, 0<d → d<a → (∑ j, if Nat.gcd a (L j) ∣ d then r.u j else 0) ≤ 1

structure OriginalProfileFacts (P : List ℕ) where
  total : P.sum=93
  positive : ∀ a∈P,3≤a
  ordered : P.Pairwise (· ≥ ·)
  row : ∀ i : Fin P.length, ProfileRow P.get (P.get i)
  cap : ∀ i j, (row i).v j≤10
  period : ∀ i, (row i).PeriodBounds
  cross : ∀ i j : Fin P.length, i≠j → CrossMoment (row i) (row j)

end Symconf93
