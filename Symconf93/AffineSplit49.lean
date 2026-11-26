module
public import Symconf93.AffineFiber49

@[expose] public section

namespace Symconf93.AffineFiber49
open scoped BigOperators

def lowCast (a : ZMod 7) : ZMod 49 := a.val

def lowReduce : ZMod 49 →+* ZMod 7 := ZMod.castHom (by decide : 7 ∣ 49) (ZMod 7)

def combineDigits (p : ZMod 7 × ZMod 7) : ZMod 49 :=
  lowCast p.1 + highLift p.2

def splitDigits (q : ZMod 49) : ZMod 7 × ZMod 7 :=
  (lowReduce q, (q.val/7 : ℕ))

theorem combine_split : ∀ q, combineDigits (splitDigits q) = q := by decide +kernel
theorem split_combine : ∀ p, splitDigits (combineDigits p) = p := by decide +kernel

def scalarDigits : (ZMod 7 × ZMod 7) ≃ ZMod 49 where
  toFun := combineDigits
  invFun := splitDigits
  left_inv := split_combine
  right_inv := combine_split

def pointwiseDigits {ι : Type*} : ((ι → ZMod 7) × (ι → ZMod 7)) ≃ (ι → ZMod 49) where
  toFun a i := combineDigits (a.1 i,a.2 i)
  invFun q := (fun i => (splitDigits (q i)).1, fun i => (splitDigits (q i)).2)
  left_inv a := Prod.ext (funext fun i => congrArg Prod.fst (split_combine (a.1 i,a.2 i)))
    (funext fun i => congrArg Prod.snd (split_combine (a.1 i,a.2 i)))
  right_inv q := funext fun i => combine_split (q i)

theorem reduce_lowCast : ∀ b : ZMod 7, lowReduce (lowCast b) = b := by decide +kernel

theorem highLift_reduce : ∀ c : ZMod 49, highLift (lowReduce c) = 7*c := by decide +kernel

theorem highLift_mul_scalar (c : ZMod 49) (b : ZMod 7) :
    c*highLift b = highLift (lowReduce c*b) := by
  calc
    c*highLift b = c*(7*lowCast b) := by rw [← highLift_reduce (lowCast b),reduce_lowCast]
    _ = 7*(c*lowCast b) := by ring
    _ = highLift (lowReduce c*b) := by rw [← highLift_reduce, map_mul, reduce_lowCast]

theorem highLift_sq_zero (u v : ZMod 7) : highLift u*highLift v=0 := by
  have h0 : (7 : ZMod 49)*7=0 := by decide +kernel
  unfold highLift
  calc
    _ = (7*7)*((u.val : ZMod 49)*v.val) := by ring
    _ = _ := by rw [h0,zero_mul]

def quad {ι : Type*} [Fintype ι] (m : ι → ι → ZMod 49) (v : ι → ZMod 49) : ZMod 49 :=
  ∑ i, ∑ j, v i * m i j * v j

def derivative {ι : Type*} [Fintype ι] (m : ι → ι → ZMod 49) (a : ι → ZMod 49) :
    ι → ZMod 7 :=
  fun j => lowReduce (2 * ∑ i, a i * m i j)

private theorem sum_highLift {ι : Type*} (s : Finset ι) (u : ι → ZMod 7) :
    (∑ i ∈ s, highLift (u i)) = highLift (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [highLift]
  | @insert a s ha ih => simp [Finset.sum_insert,ha,ih,highLift_add]

theorem quadratic_digit_expansion {ι : Type*} [Fintype ι]
    (m : ι → ι → ZMod 49) (hm : ∀ i j, m i j = m j i) (a b : ι → ZMod 7) :
    quad m (pointwiseDigits (a,b)) =
      linearFiberValue (quad m (fun i => lowCast (a i))) (derivative m (fun i => lowCast (a i))) b := by
  let l (i : ι) := lowCast (a i)
  let h (i : ι) := highLift (b i)
  have expand (i j : ι) :
      (l i+h i)*m i j*(l j+h j) = l i*m i j*l j + l i*m i j*h j + h i*m i j*l j := by
    have hz : h i*h j=0 := highLift_sq_zero _ _
    calc
      _ = l i*m i j*l j+l i*m i j*h j+h i*m i j*l j+(h i*h j)*m i j := by ring
      _ = _ := by rw [hz,zero_mul,add_zero]
  have e_cross :
      (∑ i, ∑ j,h i*m i j*l j) = ∑ i, ∑ j,l i*m i j*h j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hm j i]
    ring
  have e_sum :
      (∑ i, ∑ j,l i*m i j*h j)+(∑ i, ∑ j,l i*m i j*h j) =
        highLift (∑ j, derivative m l j*b j) := by
    rw [← two_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rw [Finset.mul_sum,← sum_highLift]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change 2*((∑ i,l i*m i j)*highLift (b j)) =
      highLift (lowReduce (2*(∑ i,l i*m i j))*b j)
    rw [←mul_assoc,highLift_mul_scalar]
  change (∑ i, ∑ j,(l i+h i)*m i j*(l j+h j)) =
    (∑ i, ∑ j,l i*m i j*l j)+highLift (∑ i,derivative m l i*b i)
  simp_rw [expand,Finset.sum_add_distrib]
  rw [e_cross,add_assoc,e_sum]

#print axioms scalarDigits
#print axioms pointwiseDigits
#print axioms quadratic_digit_expansion
end Symconf93.AffineFiber49
