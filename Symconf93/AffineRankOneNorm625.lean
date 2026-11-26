module
public import Symconf93.AffineRankOne625

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators
set_option maxHeartbeats 2500000

def bilinear {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625) (x y : ι→ZMod 625) : ZMod 625 :=
  ∑ i,∑ j,x i*m i j*y j

theorem bilinear_add_left {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625) (x y z : ι→ZMod 625) :
    bilinear m (x+y) z = bilinear m x z+bilinear m y z := by
  simp only [bilinear,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem bilinear_add_right {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625) (x y z : ι→ZMod 625) :
    bilinear m x (y+z) = bilinear m x y+bilinear m x z := by
  simp only [bilinear,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem bilinear_flip {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625)
    (hm : ∀ i j,m i j=m j i) (x y : ι→ZMod 625) :
    bilinear m x y = bilinear m y x := by
  unfold bilinear
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _=>?_ )
  refine Finset.sum_congr rfl (fun j _=>?_ )
  rw [hm j i]
  ring

theorem bilinear_const_right {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625)
    (r : ZMod 625) (hr : ∀ i, (∑ j,m i j)=r) (x : ι→ZMod 625) (s : ZMod 625) :
    bilinear m x (fun _=>s)=r*s*coordinateSum x := by
  unfold bilinear coordinateSum
  simp_rw [←Finset.sum_mul,←Finset.mul_sum,hr]
  rw [←Finset.sum_mul]
  ring

theorem quad_add_constant {ι : Type*} [Fintype ι] (m : ι→ι→ZMod 625)
    (hm : ∀ i j,m i j=m j i) (r : ZMod 625) (hr : ∀ i, (∑ j,m i j)=r)
    (x : ι→ZMod 625) (s : ZMod 625) :
    quad m (x+(fun _=>s)) = quad m x+2*r*s*coordinateSum x+(Fintype.card ι : ZMod 625)*r*s^2 := by
  change bilinear m (x+(fun _=>s)) (x+(fun _=>s)) = _
  rw [bilinear_add_left,bilinear_add_right,bilinear_add_right]
  rw [bilinear_flip m hm (fun _=>s) x]
  rw [bilinear_const_right _ r hr, bilinear_const_right _ r hr]
  change quad m x + r*s*coordinateSum x + (r*s*coordinateSum x +
        r*s*coordinateSum (fun _ : ι=>s)) = _
  simp only [coordinateSum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem quad_withOnes {ι : Type*} [Fintype ι] (h : ι→ι→ZMod 625) (x : ι→ZMod 625) :
    quad (withOnes h) x=quad h x+(coordinateSum x)^2 := by
  unfold quad withOnes coordinateSum
  simp_rw [mul_add,add_mul,mul_one,Finset.sum_add_distrib]
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem lifted_sum_reduction {ι : Type*} [Fintype ι] (a : ι→ZMod 25) :
    lowReduce (coordinateSum (fun i=>lowCast (a i)))=coordinateSum a := by
  simp [coordinateSum,map_sum,reduce_lowCast]

private theorem vanish_reduced_zero : ∀ z : ZMod 625,
    lowReduce z = 0 → z^2=0 ∧ (200:ZMod 625)*z=0 := by decide +kernel

theorem rank_one_unreduced_norm {ι : Type*} [Fintype ι] (h93 : Fintype.card ι=93)
    (h : ι→ι→ZMod 625) (hs : ∀ i j,h i j=h j i) (hr : ∀ i, (∑ j,h i j)=7)
    (a : ι→ZMod 25) (ha : action (fun i j=>lowReduce (h i j)) a=0) (s : ZMod 25) :
    quad (withOnes h) (fun i=>lowCast (a i)+lowCast s) =
      quad h (fun i=>lowCast (a i)) + (9300:ZMod 625)*(lowCast s)^2 := by
  have hsLow (i j : ι) : lowReduce (h i j)=lowReduce (h j i) := congrArg lowReduce (hs i j)
  have hrLow (i : ι) : (∑ j,lowReduce (h i j))=(7:ZMod 25) := by
    rw[←map_sum,hr]
    decide
  have z := kernel_H_sum_zero (fun i j=>lowReduce (h i j)) hsLow hrLow a ha
  let x (i : ι) := lowCast (a i)
  let t := lowCast s
  have zv : lowReduce (coordinateSum x)=0 := (lifted_sum_reduction a).trans z
  have van := vanish_reduced_zero _ zv
  have hgSym (i j : ι) : withOnes h i j=withOnes h j i := by simp [withOnes,hs i j]
  have hgSum (i : ι) : (∑ j,withOnes h i j)=(100:ZMod 625) := by
    simp only [withOnes,Finset.sum_add_distrib,hr,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,h93]
    decide
  have cross : (2:ZMod 625)*100*t*coordinateSum x=0 := by
    calc
      _ = (200*coordinateSum x)*t := by ring
      _ = _ := by rw [van.2,zero_mul]
  have E := quad_add_constant (withOnes h) hgSym 100 hgSum x t
  rw [quad_withOnes h x,van.1,add_zero,cross,add_zero,h93] at E
  have ec : ((93:ℕ):ZMod 625)*100=(9300:ZMod 625) := by decide +kernel
  rw [ec] at E
  exact E

theorem rank_one_stationary_norm {ι : Type*} [Fintype ι] (h93 : Fintype.card ι=93)
    (h : ι→ι→ZMod 625) (hs : ∀ i j,h i j=h j i) (hr : ∀ i, (∑ j,h i j)=7)
    (a : ι→ZMod 25) (ha : action (fun i j=>lowReduce (h i j)) a=0) (s : ZMod 25) :
    quad (withOnes h) (fun i=>lowCast (a i+s)) =
      quad h (fun i=>lowCast (a i))+(9300:ZMod 625)*(lowCast s)^2 := by
  have hlSym (i j : ι) : lowReduce (h i j)=lowReduce (h j i) := congrArg lowReduce (hs i j)
  have hlSum (i : ι) : (∑ j,lowReduce (h i j))=(7:ZMod 25) := by
    rw [←map_sum,hr]
    decide
  have hG := ((kernel_rank_one_split h93 (fun i j=>lowReduce (h i j)) hlSym hlSum).symm
    ((⟨a,ha⟩ : {a : ι→ZMod 25 // action (fun i j=>lowReduce (h i j)) a=0}),s)).property
  change action (withOnes (fun i j=>lowReduce (h i j))) (fun i => a i+s)=0 at hG
  have hGsym (i j : ι) : withOnes h i j=withOnes h j i := by simp [withOnes,hs i j]
  have Hd : derivative (withOnes h) (fun i=>lowCast (a i+s))=0 := by
    rw [derivative_zero_iff_kernel]
    intro j
    have e := congrFun hG j
    change ∑ i,(lowReduce (h j i)+1)*(a i+s)=0 at e
    simp only [withOnes,map_add,map_one,hs]
    simpa only [mul_comm] using e
  have e := stationary_lift_invariant (withOnes h) hGsym
    (fun i=>a i+s) Hd (fun i=>lowCast (a i)+lowCast s)
    (fun i=>by simp [map_add,reduce_lowCast])
  rw [← e]
  exact rank_one_unreduced_norm h93 h hs hr a ha s

#print axioms rank_one_unreduced_norm
#print axioms stationary_lift_invariant
#print axioms rank_one_stationary_norm
end Symconf93.AffineFiber625
