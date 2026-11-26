module
public import Symconf93.AffineKernel625

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators

def action {ι R : Type*} [Fintype ι] [CommRing R] (m : ι → ι → R) (a : ι → R) :
    ι → R := fun i => ∑ j,m i j*a j

def coordinateSum {ι R : Type*} [Fintype ι] [AddCommMonoid R] (a : ι → R) : R := ∑ i,a i

theorem action_add {ι R : Type*} [Fintype ι] [CommRing R]
    (m : ι → ι → R) (a b : ι → R) : action m (a+b) = action m a+action m b := by
  funext i
  simp only [action,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem action_sub {ι R : Type*} [Fintype ι] [CommRing R]
    (m : ι → ι → R) (a b : ι → R) : action m (a-b) = action m a-action m b := by
  funext i
  simp only [action,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem action_const {ι R : Type*} [Fintype ι] [CommRing R]
    (m : ι → ι → R) (r : R) (hr : ∀ i, (∑ j,m i j) = r) (s : R) :
    action m (fun _ => s) = (fun _ : ι => r*s) := by
  funext i
  rw [action,←Finset.sum_mul,hr]

theorem sum_action {ι R : Type*} [Fintype ι] [CommRing R]
    (m : ι → ι → R) (hm : ∀ i j,m i j=m j i)
    (r : R) (hr : ∀ i, (∑ j,m i j)=r) (x : ι → R) :
    coordinateSum (action m x)=r*coordinateSum x := by
  unfold coordinateSum action
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul]
  have he (j : ι) : (∑ i,m i j)=r := by
    exact (Finset.sum_congr rfl (fun i _ => hm i j)).trans (hr j)
  simp_rw [he,Finset.mul_sum]

def withOnes {ι R : Type*} [One R] [Add R] (h : ι → ι → R) : ι → ι → R :=
  fun i j => h i j+1

theorem action_withOnes {ι R : Type*} [Fintype ι] [CommRing R]
    (h : ι → ι → R) (a : ι → R) (i : ι) :
    action (withOnes h) a i = action h a i+coordinateSum a := by
  simp [action,withOnes,coordinateSum,add_mul,Finset.sum_add_distrib]

theorem kernel_H_sum_zero {ι : Type*} [Fintype ι] (h : ι → ι → ZMod 25)
    (hs : ∀ i j,h i j=h j i) (hr : ∀ i, (∑ j,h i j)=7)
    (a : ι → ZMod 25) (ha : action h a=0) : coordinateSum a=0 := by
  have E := sum_action h hs 7 hr a
  rw [ha] at E
  change (∑ i : ι,(0 : ZMod 25)) = _ at E
  simp only [Finset.sum_const_zero] at E
  have u : (18 : ZMod 25)*7 = 1 := by decide +kernel
  have E' := congrArg (fun z : ZMod 25 => 18*z) E.symm
  simpa only [←mul_assoc,u,one_mul,mul_zero] using E'

private theorem sum_const93 {ι : Type*} [Fintype ι] (h93 : Fintype.card ι=93) (s : ZMod 25) :
    coordinateSum (fun _ : ι => s)=93*s := by
  simp [coordinateSum,nsmul_eq_mul,h93]

/-- The actual rank-one Gram addition does not require a 93-dimensional
change-of-basis certificate: the stationary split is sum-zero H-kernel plus
one independent constant direction, over Z/25. -/
noncomputable def kernel_rank_one_split {ι : Type*} [Fintype ι] (h93 : Fintype.card ι = 93)
    (h : ι → ι → ZMod 25) (hs : ∀ i j,h i j=h j i)
    (hr : ∀ i,(∑ j,h i j)=7) :
    {a : ι → ZMod 25 // action (withOnes h) a=0} ≃
      {a : ι → ZMod 25 // action h a=0} × ZMod 25 where
  toFun a :=
    let s := 7*coordinateSum a.val
    ⟨⟨a.val-(fun _ => s), by
        funext i
        have e := congrFun a.property i
        rw [action_withOnes] at e
        rw [action_sub,Pi.sub_apply,action_const h 7 hr]
        change action h a.val i + coordinateSum a.val=0 at e
        change action h a.val i-7*s=0
        have zz : (1:ZMod 25)+7*7=0 := by decide +kernel
        have es : 7*s = -coordinateSum a.val := by
          have W : ((1:ZMod 25)+7*7)*coordinateSum a.val = 0 := by rw [zz,zero_mul]
          simp only [s,add_mul,one_mul,mul_assoc] at W ⊢
          linear_combination W
        rw [es,sub_neg_eq_add,e]⟩,s⟩
  invFun as :=
    ⟨as.1.val+(fun _ => as.2), by
      funext i
      rw [action_withOnes,action_add,Pi.add_apply,as.1.property,action_const h 7 hr]
      have z := kernel_H_sum_zero h hs hr as.1.val as.1.property
      have e : coordinateSum (as.1.val+(fun _ => as.2))=93*as.2 := by
        simp only [coordinateSum,Pi.add_apply,Finset.sum_add_distrib]
        exact (by
          change coordinateSum as.1.val+coordinateSum (fun _ : ι => as.2)=_
          rw [z,sum_const93 h93,zero_add])
      rw [e]
      change 0 + 7*as.2+93*as.2=0
      rw [zero_add,←add_mul]
      have q : (7:ZMod 25)+93=0 := by decide +kernel
      rw [q,zero_mul]⟩
  left_inv := by
    intro a
    apply Subtype.ext
    funext i
    simp
  right_inv := by
    intro as
    have z := kernel_H_sum_zero h hs hr as.1.val as.1.property
    have es : (7:ZMod 25)*coordinateSum (as.1.val+(fun _=>as.2))=as.2 := by
      have ee : coordinateSum (as.1.val+(fun _=>as.2)) =
          coordinateSum as.1.val+coordinateSum (fun _ : ι => as.2) := by
        simp only [coordinateSum,Pi.add_apply,Finset.sum_add_distrib]
      rw [ee,z,zero_add,sum_const93 h93,←mul_assoc]
      have u : (7 : ZMod 25)*93=1 := by decide +kernel
      rw [u,one_mul]
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change as.1.val i+as.2-(7*coordinateSum (as.1.val+(fun _=>as.2)))=as.1.val i
      rw [es,add_sub_cancel_right]
    · exact es

#print axioms kernel_rank_one_split
end Symconf93.AffineFiber625
