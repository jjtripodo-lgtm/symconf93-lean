module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Symconf93.OffsetMoments
open scoped BigOperators
abbrev F := ZMod 31

def tVal (sa sb sc : F) : F := -28 * (sa+sb+sc)
def bVal (sb sc t : F) : F := 2*sb+28*sc+t
def dVal (qa qb qc sc t : F) : F := qa+qb+qc+2*t*sc+10*t^2

theorem translate_first (sa sb sc x y : F)
    (h : sa+sb+sc+15*x+10*y=0) : y = tVal sa sb sc + 14*x := by
  have hm : (28:F)*10=1 := by decide
  have hc : -(28:F)*15=14 := by decide
  have hy : 10*y= -(sa+sb+sc+15*x) := eq_neg_of_add_eq_zero_right h
  calc
    y = 28*(10*y) := by rw [←mul_assoc,hm,one_mul]
    _ = 28*(-(sa+sb+sc+15*x)) := by rw [hy]
    _ = tVal sa sb sc + (-(28:F)*15)*x := by unfold tVal; ring
    _ = _ := by rw [hc]

theorem translate_second (sb sc qa qb qc t x y : F)
    (hy : y=t+14*x)
    (h : qa+qb+qc+2*x*sb+15*x^2+2*y*sc+10*y^2=0) :
    22*x^2 + (bVal sb sc t)*x + dVal qa qb qc sc t = 0 := by
  have h1 : (15:F)+10*14^2=22 := by decide
  have h2 : (20:F)*14=1 := by decide
  rw [hy] at h
  calc
    _ = ((15:F)+10*14^2)*x^2 +
          (2*sb+28*sc+((20:F)*14)*t)*x + dVal qa qb qc sc t := by rw [h1,h2,one_mul]; rfl
    _ = qa+qb+qc+2*x*sb+15*x^2+2*(t+14*x)*sc+10*(t+14*x)^2 := by unfold dVal; ring
    _ = 0 := h

theorem discriminant_candidate (x B D : F) (h : 22*x^2+B*x+D=0) :
    ∃ r : F, r^2=B^2-88*D ∧ x=12*(r-B) := by
  refine ⟨44*x+B, ?_, ?_⟩
  · have h0 : (88:F)*(22*x^2+B*x+D)=0 := by rw [h,mul_zero]
    have h1 : (44*x+B)^2 - (B^2-88*D)=(88:F)*(22*x^2+B*x+D) := by ring
    rw [h0, sub_eq_zero] at h1
    exact h1
  · have h12 : (12:F)*44=1 := by decide
    calc
      x = ((12:F)*44)*x := by rw [h12,one_mul]
      _ = 12*(44*x+B-B) := by ring

def moment (S : Finset F) (k : Nat) : F := ∑ z ∈ S, z^k
def shifted (S : Finset F) (x : F) (k : Nat) : F := ∑ z ∈ S, (z+x)^k

theorem third_shift (S : Finset F) (x : F) :
    shifted S x 3 = moment S 3 + 3*x*moment S 2 +
      3*x^2*moment S 1 + (S.card : F)*x^3 := by
  calc
    _ = ∑ z ∈ S, (z^3+3*x*z^2+3*x^2*z+x^3) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      simp [moment, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.mul_sum]

theorem fourth_shift (S : Finset F) (x : F) :
    shifted S x 4 = moment S 4 + 4*x*moment S 3 +
      6*x^2*moment S 2 + 4*x^3*moment S 1 + (S.card : F)*x^4 := by
  calc
    _ = ∑ z ∈ S, (z^4+4*x*z^3+6*x^2*z^2+4*x^3*z+x^4) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      simp [moment, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.mul_sum]

#print axioms translate_first
#print axioms translate_second
#print axioms discriminant_candidate
#print axioms third_shift
#print axioms fourth_shift
end Symconf93.OffsetMoments
