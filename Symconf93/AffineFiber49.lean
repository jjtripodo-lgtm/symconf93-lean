module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

namespace Symconf93.AffineFiber49
open scoped BigOperators

/-- The top digits embed additively, but not multiplicatively. -/
def highLift (x : ZMod 7) : ZMod 49 := 7 * (x.val : ZMod 49)

private theorem clearHighMod (n : ℕ) :
    (7 : ZMod 49) * ((n%7 : ℕ) : ZMod 49) = 7 * (n : ZMod 49) := by
  have nsplit : n%7 + 7*(n/7) = n := Nat.mod_add_div n 7
  have e : ((n%7 : ℕ) : ZMod 49) + 7*((n/7 : ℕ) : ZMod 49) = (n : ZMod 49) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ZMod 49)) nsplit
  have z : (7 : ZMod 49)*7 = 0 := by decide +kernel
  rw [←e,mul_add,←mul_assoc,z,zero_mul,add_zero]

theorem highLift_add (a b : ZMod 7) : highLift (a+b) = highLift a+highLift b := by
  unfold highLift
  rw [ZMod.val_add,clearHighMod, Nat.cast_add,mul_add]

theorem highLift_one : highLift 1 = 7 := by decide +kernel

private def inverseAtOne (a : ZMod 7) : ZMod 7 :=
  ((List.finRange 7).find? (fun u => a*(u.val : ZMod 7)=1)).getD 0 |>.val

private theorem oneDivisor_check : ∀ a : ZMod 7,
    a ≠ 0 → a * inverseAtOne a = 1 := by decide +kernel

theorem one_divisor (a : ZMod 7) (ha : a ≠ 0) :
    ∃ u : ZMod 7, a*u = 1 := ⟨inverseAtOne a,oneDivisor_check a ha⟩

def linearFiberValue {ι : Type*} [Fintype ι] (q₀ : ZMod 49) (f b : ι → ZMod 7) :
    ZMod 49 := q₀ + highLift (∑ i,f i*b i)

/-- If an actual affine fibre has a nonzero coefficient then an explicit
single-coordinate translation pairs its 0 and 7 level sets. This uses no
Gram inverse or diagonalization and holds for every nonzero residue in the prime field. -/
theorem nonzero_affine_fiber {ι : Type*} [Fintype ι] (q₀ : ZMod 49)
    (f : ι → ZMod 7) (hf : f ≠ 0) :
    Nat.card {b : ι → ZMod 7 // linearFiberValue q₀ f b = 0} =
      Nat.card {b : ι → ZMod 7 // linearFiberValue q₀ f b = 7} := by
  classical
  have he : ∃ i, f i ≠ 0 := by
    by_contra! H
    apply hf
    funext i
    exact H i
  obtain ⟨i,hi⟩ := he
  obtain ⟨u,hu⟩ := one_divisor (f i) hi
  let d : ι → ZMod 7 := fun j => if j=i then u else 0
  have dot : ∑ j, f j*d j = 1 := by
    simp [d,mul_ite,hu]
  have shift (b : ι → ZMod 7) :
      linearFiberValue q₀ f (b+d) = linearFiberValue q₀ f b + 7 := by
    unfold linearFiberValue
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,highLift_add,dot,highLift_one,add_assoc]
  let join : {b : ι → ZMod 7 // linearFiberValue q₀ f b = 0} ≃
      {b : ι → ZMod 7 // linearFiberValue q₀ f b = 7} :=
    { toFun := fun b => ⟨b.val+d, by rw [shift,b.property,zero_add]⟩
      invFun := fun b => ⟨b.val-d,by
        have h := shift (b.val-d)
        rw [sub_add_cancel,b.property] at h
        exact (add_right_cancel (h.symm.trans (zero_add _).symm))⟩
      left_inv := by intro b; apply Subtype.ext; exact add_sub_cancel_right _ _
      right_inv := by intro b; apply Subtype.ext; exact sub_add_cancel _ _ }
  exact Nat.card_congr join

#print axioms highLift_add
#print axioms one_divisor
#print axioms nonzero_affine_fiber
end Symconf93.AffineFiber49
