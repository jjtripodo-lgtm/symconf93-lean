module
public import Symconf93.AffineSplit625

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators

/-- The stationary equation is the ordinary reduced Gram kernel, with no
projective or punctured-vertex convention. -/
theorem derivative_zero_iff_kernel {ι : Type*} [Fintype ι]
    (m : ι → ι → ZMod 625) (a : ι → ZMod 25) :
    derivative m (fun i => lowCast (a i)) = 0 ↔
      ∀ j, ∑ i, a i*lowReduce (m i j) = 0 := by
  have hs (j : ι) : derivative m (fun i => lowCast (a i)) j =
      2*(∑ i, a i*lowReduce (m i j)) := by
    simp only [derivative,map_mul,map_ofNat,map_sum,reduce_lowCast]
  constructor
  · intro h j
    have e := congrFun h j
    rw [hs] at e
    change 2*(∑ i, a i*lowReduce (m i j)) = 0 at e
    have u : (13:ZMod 25)*2 = 1 := by decide +kernel
    have e' := congrArg (fun z : ZMod 25 => 13*z) e
    simpa only [←mul_assoc,u,one_mul,mul_zero] using e'
  · intro h
    funext j
    rw [hs,h j,mul_zero]
    rfl

/-- On a stationary low digit, replacing its literal representative by
any other canonical/uncanonical lift cannot change the mod-625 norm. -/
theorem stationary_lift_invariant {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625)
    (hm : ∀ i j,m i j=m j i) (a : ι→ZMod 25)
    (ha : derivative m (fun i=>lowCast (a i))=0)
    (x : ι→ZMod 625) (hx : ∀ i,lowReduce (x i)=a i) :
    quad m x = quad m (fun i=>lowCast (a i)) := by
  let b (i : ι) := (splitDigits (x i)).2
  have hab : (pointwiseDigits (a,b))=x := by
    have E := (pointwiseDigits (ι:=ι)).apply_symm_apply x
    have C : ((pointwiseDigits (ι:=ι)).symm x)=(a,b) := by
      apply Prod.ext
      · exact funext hx
      · rfl
    rw [C] at E
    exact E
  rw [←hab,quadratic_digit_expansion m hm]
  simp [linearFiberValue,ha,highLift]

#print axioms derivative_zero_iff_kernel
#print axioms stationary_lift_invariant
end Symconf93.AffineFiber625
