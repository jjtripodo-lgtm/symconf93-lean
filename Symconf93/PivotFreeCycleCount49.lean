module
public import Symconf93.PivotFreeProfile49

@[expose] public section

/-! The surviving constant cycle lift is counted by the joint weighted
sum and square sum in characteristic seven. No rational congruence or
negative count input is used in this transport. -/
namespace Symconf93.AffineFiber49
open Symconf59 Matrix
open scoped BigOperators Matrix

private theorem lowSum_square_zero49 :
    ∀ s : ZMod 49, lowReduce s=0 → s*s=0 := by decide +kernel

private theorem highLift_inj49 : Function.Injective highLift := by
  intro x y
  exact (show ∀ x y : ZMod 7,highLift x=highLift y → x=y by decide +kernel) x y

theorem low_quad_on_critical_constants49 (P : List Nat) (c : Fin P.length→ZMod 7)
    (h : (jointValue P c).1=0) :
    lowQuad (profileForm49 P) (cycleConstant49 P c)=highLift (jointValue P c).2 := by
  let a : BlocksOf P→ZMod 49 := lowCast ∘ cycleConstant49 P c
  let s : ZMod 49 := ∑i,a i
  have hs : lowReduce s=0 := by
    dsimp only [s,a]
    rw [map_sum]
    simp only [Function.comp_apply,reduce_lowCast,sum_cycleConstant49,h]
  have hs2 := lowSum_square_zero49 s hs
  have h2 : lowReduce (∑i,a i*a i)=(jointValue P c).2 := by
    rw [map_sum,Fintype.sum_sigma,jointValue_snd]
    simp [a,cycleConstant49,nsmul_eq_mul,mul_assoc,reduce_lowCast]
  change quad (profileForm49 P) a=_
  rw [←gramNorm_eq_quad49]
  unfold gramNorm dotProduct
  calc
    _ = ∑ i, a i*(7*a i+s) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [form_mv49]
      simp only [a,Function.comp_apply,cycleConstant49,siteNext,sitePrev]
      change lowCast (c i.1)*(9*lowCast (c i.1)+s-lowCast (c i.1)-lowCast (c i.1))=_
      ring
    _ = 7*(∑i,a i*a i)+s*s := by
      simp_rw [mul_add,Finset.sum_add_distrib,←Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hs2,add_zero,←highLift_reduce,h2]

/-- A critical low digit is in bijection with one real cycle value per
physical component. The zero weighted sum and the specified quadratic
lift are both part of the target. -/
theorem card_critical_is_joint49 {P : List Nat} (hP : 0<P.length)
    (hL : ∀ b : Fin P.length,(P.get b:ZMod 7)≠0) (t : ZMod 7) :
    Nat.card {a : Digits (BlocksOf P) // lowDeriv (profileForm49 P) a=0 ∧
      lowQuad (profileForm49 P) a=highLift t} = jointCount P (0,t) := by
  let F (a : Digits (BlocksOf P)) : Fin P.length→ZMod 7 :=
    fun i=>a ⟨i,startCycle49 hL i⟩
  have toJoint (a : Digits (BlocksOf P))
      (ha : lowDeriv (profileForm49 P) a=0)
      (hqa : lowQuad (profileForm49 P) a=highLift t) :
      jointValue P (F a)=(0,t) := by
    obtain ⟨he,hs⟩ := (derivative_kernel49 hP hL a).mp ha
    have hE : a=cycleConstant49 P (F a) := he
    have hz : (jointValue P (F a)).1=0 := by
      rw [←sum_cycleConstant49,←hE,hs]
    apply Prod.ext hz
    apply highLift_inj49
    rw [←low_quad_on_critical_constants49 _ _ hz,←hE,hqa]
  have fromJoint (c : Fin P.length→ZMod 7) (h : jointValue P c=(0,t)) :
      lowDeriv (profileForm49 P) (cycleConstant49 P c)=0 ∧
      lowQuad (profileForm49 P) (cycleConstant49 P c)=highLift t := by
    have h0 : (jointValue P c).1=0 := congrArg Prod.fst h
    have ht : (jointValue P c).2=t := congrArg Prod.snd h
    constructor
    · apply (derivative_kernel49 hP hL _).mpr
      exact ⟨rfl,(sum_cycleConstant49 _ _).trans h0⟩
    · rw [low_quad_on_critical_constants49 _ _ h0,ht]
  unfold jointCount
  apply Nat.card_congr
  exact {
    toFun := fun a=>⟨F a.val,toJoint a.val a.property.1 a.property.2⟩
    invFun := fun c=>⟨cycleConstant49 P c.val,fromJoint c.val c.property⟩
    left_inv := fun a=>Subtype.ext ((derivative_kernel49 hP hL _).mp a.property.1).1.symm
    right_inv := fun _=>rfl
  }

theorem true_cycle_contrast49 {P : List Nat} (hP : 0<P.length)
    (hL : ∀ b : Fin P.length,(P.get b:ZMod 7)≠0) :
    contrast (gramNorm (Symconf59.reduceMatrix 49 (profileGram93 P))) (7:ZMod 49) =
      (7:ℤ)^Fintype.card (BlocksOf P) *
        ((jointCount P (0,0):ℤ)-jointCount P (0,1)) := by
  rw [←form_is_original49,gramNorm_eq_quad49,pivotFree_critical_contrast49 _
    (form_symm49 P)]
  rw [show (0:ZMod 49)=highLift 0 by decide +kernel,
    show (7:ZMod 49)=highLift 1 by decide +kernel,
    card_critical_is_joint49 hP hL,card_critical_is_joint49 hP hL]

end Symconf93.AffineFiber49

#print axioms Symconf93.AffineFiber49.card_critical_is_joint49
#print axioms Symconf93.AffineFiber49.true_cycle_contrast49
