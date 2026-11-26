module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators

/-- The top digits embed additively, but not multiplicatively. -/
def highLift (x : ZMod 25) : ZMod 625 := 25 * (x.val : ZMod 625)

private theorem clearHighMod (n : ℕ) :
    (25 : ZMod 625) * ((n%25 : ℕ) : ZMod 625) = 25 * (n : ZMod 625) := by
  have nsplit : n%25 + 25*(n/25) = n := Nat.mod_add_div n 25
  have e : ((n%25 : ℕ) : ZMod 625) + 25*((n/25 : ℕ) : ZMod 625) = (n : ZMod 625) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ZMod 625)) nsplit
  have z : (25 : ZMod 625)*25 = 0 := by decide +kernel
  rw [←e,mul_add,←mul_assoc,z,zero_mul,add_zero]

theorem highLift_add (a b : ZMod 25) : highLift (a+b) = highLift a+highLift b := by
  unfold highLift
  rw [ZMod.val_add,clearHighMod, Nat.cast_add,mul_add]

theorem highLift_five : highLift 5 = 125 := by decide +kernel

private def inverseAtFive (a : ZMod 25) : ZMod 25 :=
  ((List.finRange 25).find? (fun u => a*(u.val : ZMod 25)=5)).getD 0 |>.val

private theorem fiveDivisor_check : ∀ a : ZMod 25,
    a ≠ 0 → a * inverseAtFive a = 5 := by decide +kernel

theorem five_divisor (a : ZMod 25) (ha : a ≠ 0) :
    ∃ u : ZMod 25, a*u = 5 := ⟨inverseAtFive a,fiveDivisor_check a ha⟩

def linearFiberValue {ι : Type*} [Fintype ι] (q₀ : ZMod 625) (f b : ι → ZMod 25) :
    ZMod 625 := q₀ + highLift (∑ i,f i*b i)

/-- If an actual affine fibre has a nonzero coefficient then an explicit
single-coordinate translation pairs its 0 and 125 level sets. This uses no
Gram inverse or diagonalization and holds even for a nonunit coefficient. -/
theorem nonzero_affine_fiber {ι : Type*} [Fintype ι] (q₀ : ZMod 625)
    (f : ι → ZMod 25) (hf : f ≠ 0) :
    Nat.card {b : ι → ZMod 25 // linearFiberValue q₀ f b = 0} =
      Nat.card {b : ι → ZMod 25 // linearFiberValue q₀ f b = 125} := by
  classical
  have he : ∃ i, f i ≠ 0 := by
    by_contra! H
    apply hf
    funext i
    exact H i
  obtain ⟨i,hi⟩ := he
  obtain ⟨u,hu⟩ := five_divisor (f i) hi
  let d : ι → ZMod 25 := fun j => if j=i then u else 0
  have dot : ∑ j, f j*d j = 5 := by
    simp [d,mul_ite,hu]
  have shift (b : ι → ZMod 25) :
      linearFiberValue q₀ f (b+d) = linearFiberValue q₀ f b + 125 := by
    unfold linearFiberValue
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,highLift_add,dot,highLift_five,add_assoc]
  let join : {b : ι → ZMod 25 // linearFiberValue q₀ f b = 0} ≃
      {b : ι → ZMod 25 // linearFiberValue q₀ f b = 125} :=
    { toFun := fun b => ⟨b.val+d, by rw [shift,b.property,zero_add]⟩
      invFun := fun b => ⟨b.val-d,by
        have h := shift (b.val-d)
        rw [sub_add_cancel,b.property] at h
        exact (add_right_cancel (h.symm.trans (zero_add _).symm))⟩
      left_inv := by intro b; apply Subtype.ext; exact add_sub_cancel_right _ _
      right_inv := by intro b; apply Subtype.ext; exact sub_add_cancel _ _ }
  exact Nat.card_congr join

#print axioms highLift_add
#print axioms five_divisor
#print axioms nonzero_affine_fiber
end Symconf93.AffineFiber625
