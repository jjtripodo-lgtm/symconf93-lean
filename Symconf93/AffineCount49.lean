module
public import Symconf93.AffineSplit49
public import Symconf93.GramSign93
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-! Literal low/high digit decomposition. Every noncritical low digit
pairs its full high-digit fibers by a coordinate translation. Each
surviving low digit has all 7^card(ι) high lifts, with no cancellation
by division and no substituted diagonal form. -/
namespace Symconf93.AffineFiber49
open scoped BigOperators

abbrev Digits (ι : Type*) := ι→ZMod 7

def lowQuad {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 49) (a : Digits ι) : ZMod 49 :=
  quad m (lowCast ∘ a)

def lowDeriv {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 49) (a : Digits ι) : Digits ι :=
  derivative m (lowCast ∘ a)

def affineDigits {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 49) (p : Digits ι × Digits ι) : ZMod 49 :=
  linearFiberValue (lowQuad m p.1) (lowDeriv m p.1) p.2

private theorem card_digit_transport {ι : Type*} [Fintype ι]
    (m : ι→ι→ZMod 49) (hm : ∀ i j, m i j=m j i) (t : ZMod 49) :
    Nat.card {v : ι→ZMod 49 // quad m v=t} =
      Nat.card {p : Digits ι × Digits ι // affineDigits m p=t} := by
  apply Nat.card_congr
  exact (Equiv.subtypeEquiv pointwiseDigits (fun p => by
    rw [quadratic_digit_expansion m hm p.1 p.2]; rfl)).symm

private theorem affine_at_critical {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 49)
    (a b : Digits ι) (ha : lowDeriv m a=0) :
    affineDigits m (a,b)=lowQuad m a := by
  unfold affineDigits linearFiberValue
  simp [ha,highLift]

private theorem card_critical_digits {ι : Type*} [Fintype ι]
    (m : ι→ι→ZMod 49) (t : ZMod 49) :
    Nat.card {p : Digits ι × Digits ι // lowDeriv m p.1=0 ∧ affineDigits m p=t} =
    Nat.card {a : Digits ι // lowDeriv m a=0 ∧ lowQuad m a=t} * (7^Fintype.card ι) := by
  classical
  let e :
      {p : Digits ι × Digits ι // lowDeriv m p.1=0 ∧ affineDigits m p=t} ≃
      ({a : Digits ι // lowDeriv m a=0 ∧ lowQuad m a=t} × Digits ι) :=
    {toFun := fun ⟨⟨a,b⟩,ha,ht⟩ => (⟨a,ha,(affine_at_critical m a b ha).symm.trans ht⟩,b)
     invFun := fun ⟨⟨a,ha,ht⟩,b⟩ => ⟨(a,b),ha,(affine_at_critical m a b ha).trans ht⟩
     left_inv := by rintro ⟨⟨a,b⟩,ha,ht⟩; rfl
     right_inv := by rintro ⟨⟨a,ha,ht⟩,b⟩; rfl}
  rw [Nat.card_congr e,Nat.card_prod,Nat.card_eq_fintype_card (α:=Digits ι),
    Fintype.card_pi,Finset.prod_const,Finset.card_univ]
  congr 2

private theorem card_noncritical_as_sigma {ι : Type*} [Fintype ι]
    (m : ι→ι→ZMod 49) (t : ZMod 49) :
    Nat.card {p : Digits ι × Digits ι // lowDeriv m p.1≠0 ∧ affineDigits m p=t} =
    Nat.card (Σ a : {a : Digits ι // lowDeriv m a≠0},
        {b : Digits ι // linearFiberValue (lowQuad m a.val) (lowDeriv m a.val) b=t}) := by
  apply Nat.card_congr
  exact {toFun := fun ⟨⟨a,b⟩,ha,hb⟩ => ⟨⟨a,ha⟩,⟨b,hb⟩⟩
         invFun := fun ⟨⟨a,ha⟩,⟨b,hb⟩⟩ => ⟨(a,b),ha,hb⟩
         left_inv := by rintro ⟨⟨a,b⟩,ha,hb⟩; rfl
         right_inv := by rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩; rfl}

private theorem noncritical_cancels {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 49) :
    Nat.card {p : Digits ι × Digits ι // lowDeriv m p.1≠0 ∧ affineDigits m p=0} =
    Nat.card {p : Digits ι × Digits ι // lowDeriv m p.1≠0 ∧ affineDigits m p=7} := by
  classical
  rw [card_noncritical_as_sigma,card_noncritical_as_sigma,Nat.card_sigma,Nat.card_sigma]
  exact Finset.sum_congr rfl (fun a _=>nonzero_affine_fiber _ _ a.property)

theorem pivotFree_critical_contrast49 {ι : Type*} [Fintype ι]
    (m : ι→ι→ZMod 49) (hm : ∀ i j, m i j=m j i) :
    contrast (quad m) (7:ZMod 49) =
      (7:ℤ)^Fintype.card ι *
      ((Nat.card {a : Digits ι // lowDeriv m a=0 ∧ lowQuad m a=0}:ℤ) -
        Nat.card {a : Digits ι // lowDeriv m a=0 ∧ lowQuad m a=7}) := by
  unfold contrast
  rw [card_digit_transport m hm,card_digit_transport m hm,
    count_norm_partition (affineDigits m) (fun p=>lowDeriv m p.1=0) 0,
    count_norm_partition (affineDigits m) (fun p=>lowDeriv m p.1=0) 7,
    noncritical_cancels,card_critical_digits,card_critical_digits]
  push_cast
  ring

theorem gramNorm_eq_quad49 {ι : Type*} [Fintype ι] (m : Matrix ι ι (ZMod 49)) :
    gramNorm m=quad m := by
  funext x
  unfold gramNorm quad Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum,mul_assoc]

end Symconf93.AffineFiber49

#print axioms Symconf93.AffineFiber49.pivotFree_critical_contrast49
