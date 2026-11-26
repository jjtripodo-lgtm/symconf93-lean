module
public import Symconf93.Actual31Terminal
public import Symconf93.EvenCatalogueProof93
public import Symconf93.CompactCoverage93

@[expose] public section

/-! Private assembly on exact original definitions. The 25 negative-
contrast exclusions and the checked coverage root remain explicit
premises here; no weakened-incidence or periodicity premise is added. -/
namespace Symconf93
open Matrix
open scoped Matrix

def oddArithmeticProfiles93 : List (List ℕ) :=
  profiles37.filter fun P => decide (P.length%2=1 ∧ P≠P31 ∧ P≠Mixed37)

theorem oddArithmeticProfiles93_count : oddArithmeticProfiles93.length=25 := by decide

theorem mem_oddArithmeticProfiles93 {P : List ℕ} :
    P∈oddArithmeticProfiles93 ↔ P∈profiles37 ∧ P.length%2=1 ∧ P≠P31 ∧ P≠Mixed37 := by
  simp [oddArithmeticProfiles93]

/-- The only arithmetic premise left after the even and original
residual formal proofs. Exact physical matrix, exact descending list. -/
def OddArithmetic93 : Prop := ∀ P : List ℕ, P∈oddArithmeticProfiles93 →
  ¬∃ A : Matrix (BlocksOf P) (BlocksOf P) ℤ, profileGram93 P=A*Aᵀ

theorem arithmetic93_of_pinned_odd (hOdd : OddArithmetic93) : Arithmetic93 := by
  apply Arithmetic93_of_odd_rows
  intro P hP hParity h31 hMix
  exact hOdd P (mem_oddArithmeticProfiles93.mpr ⟨hP,hParity,h31,hMix⟩)

theorem no_unrestricted_incidence93_of_coverage_and_odd_arithmetic
    (hC : Coverage93) (hOdd : OddArithmetic93) : ¬∃ A : Int93, Incidence93 A :=
  no_unrestricted_incidence93_of_coverage_and_arithmetic hC (arithmetic93_of_pinned_odd hOdd)

theorem no_unrestricted_incidence93_of_compact_root_and_odd_arithmetic
    (hC : NodeCoverage93 [] 93 93) (hOdd : OddArithmetic93) :
    ¬∃ A : Int93, Incidence93 A :=
  no_unrestricted_incidence93_of_coverage_and_odd_arithmetic (coverage93_of_root hC) hOdd

end Symconf93

#print axioms Symconf93.oddArithmeticProfiles93_count
#print axioms Symconf93.arithmetic93_of_pinned_odd
#print axioms Symconf93.no_unrestricted_incidence93_of_coverage_and_odd_arithmetic
#print axioms Symconf93.no_unrestricted_incidence93_of_compact_root_and_odd_arithmetic
