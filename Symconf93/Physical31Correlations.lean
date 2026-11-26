module
public import Symconf93.OddBlock
public import Mathlib.Tactic.Abel

@[expose] public section

/-! Physical within-block and fixed-other-row correlations. Reflection is
independent in each shared column; a global cyclic action is unnecessary. -/
namespace Symconf93
open Symconf59
open scoped BigOperators

abbrev Z31 := ZMod 31

def cycleCorr31 (f g : Z31 → ℤ) (d : Z31) : ℤ :=
  ∑ z, f (z-d)*g z

def cycleAuto31 (f : Z31 → ℤ) (d : Z31) : ℤ := cycleCorr31 f f d

private theorem sum_shift (f : Z31 → ℤ) (t : Z31) :
    (∑ x, f (x+t))=∑ x, f x := Equiv.sum_comp (Equiv.addRight t) f

private theorem sum_neg (f : Z31 → ℤ) :
    (∑ x, f (-x))=∑ x, f x := Equiv.sum_comp (Equiv.neg _) f

theorem cycleAuto31_neg (f : Z31 → ℤ) (d : Z31) :
    cycleAuto31 f (-d)=cycleAuto31 f d := by
  unfold cycleAuto31 cycleCorr31
  have hh := sum_shift (fun z => f (z-(-d))*f z) (-d)
  simp [sub_eq_add_neg,add_assoc] at hh
  calc
    _ = ∑ x, f x * f (x+ -d) := by simpa only [sub_neg_eq_add] using hh.symm
    _ = _ := by simp only [sub_eq_add_neg,mul_comm]

theorem cycleAuto31_reflection (f : Z31 → ℤ) (d : Z31) :
    cycleAuto31 (fun z => f (-z)) d=cycleAuto31 f d := by
  rw [← cycleAuto31_neg f d]
  unfold cycleAuto31 cycleCorr31
  have h := sum_neg (fun z => f (z-(-d))*f z)
  simpa [sub_eq_add_neg,neg_add,add_comm] using h

/-- Actual left and right Gram correlations at a physical shift both
give the autocorrelation of its first-row support. -/
theorem binary31_block_same_signature (A : Z31 → Z31 → ℤ)
    (hw : BlockWave A) (hb : ∀ i j, A i j=0 ∨ A i j=1) (d : Z31) :
    (∑ z, A 0 z*A d z)=cycleAuto31 (A 0) d ∧
      (∑ z, A z 0*A z d)=cycleAuto31 (A 0) d := by
  rcases binary31_block_orientation A hw hb with ⟨f,h⟩|⟨f,h⟩
  · have h0 : A 0=f := by funext z; rw [h,sub_zero]
    rw [h0]
    constructor
    · simp only [h,cycleAuto31,cycleCorr31,mul_comm]
    · simp only [h,zero_sub]
      have hN := sum_neg (fun z => f z*f (d+z))
      calc
        _ = ∑ z, f z*f (d+z) := by
          simpa only [sub_eq_add_neg] using hN
        _ = cycleAuto31 f (-d) := by
          simp only [cycleAuto31,cycleCorr31,sub_neg_eq_add,add_comm,mul_comm]
        _ = _ := cycleAuto31_neg f d
  · have h0 : A 0=f := by funext z; rw [h,add_zero]
    rw [h0,← cycleAuto31_neg f d]
    constructor
    · simp only [h,cycleAuto31,cycleCorr31,sub_neg_eq_add,mul_comm]
    · simp only [h,add_zero,cycleAuto31,cycleCorr31,sub_neg_eq_add,add_comm,mul_comm]

/-- Compare all rows of the first block against ONE physical row of the
second block. Only the first block needs an orientation. If reversed,
both first-row supports are reflected in this single column. This
simultaneously preserves their native signatures, hence also preserves
column disjointness tests. -/
theorem binary31_fixed_cross_pair (A B : Z31 → Z31 → ℤ)
    (hw : BlockWave A) (hb : ∀ i j, A i j=0 ∨ A i j=1) :
    ∃ f g : Z31 → ℤ,
      (∀ d, (∑ z, A d z * B 0 z)=cycleCorr31 f g d) ∧
      (∀ d, cycleAuto31 f d=cycleAuto31 (A 0) d) ∧
      (∀ d, cycleAuto31 g d=cycleAuto31 (B 0) d) ∧
      (∑ z, f z)=(∑ z,A 0 z) ∧ (∑ z, g z)=(∑ z,B 0 z) ∧
      ((∀ z, f z=A 0 z ∧ g z=B 0 z) ∨
       (∀ z, f z=A 0 (-z) ∧ g z=B 0 (-z))) := by
  rcases binary31_block_orientation A hw hb with ⟨p,h⟩|⟨p,h⟩
  · refine ⟨A 0,B 0,?_,fun _ => rfl,fun _ => rfl,rfl,rfl,Or.inl fun _ => ⟨rfl,rfl⟩⟩
    intro d
    simp only [cycleCorr31,h,sub_zero]
  · refine ⟨fun z => A 0 (-z),fun z => B 0 (-z),?_,
      cycleAuto31_reflection (A 0),cycleAuto31_reflection (B 0),
      sum_neg (A 0),sum_neg (B 0),Or.inr fun _ => ⟨rfl,rfl⟩⟩
    intro d
    have hN := sum_neg (fun z => p (z+d) * B 0 z)
    simp only [cycleCorr31,h,add_zero,sub_eq_add_neg,neg_add,neg_neg,add_comm] at hN ⊢
    exact hN.symm

end Symconf93

#print axioms Symconf93.binary31_block_same_signature
#print axioms Symconf93.binary31_fixed_cross_pair
