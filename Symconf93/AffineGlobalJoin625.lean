module
public import Symconf93.AffineRankOneNorm625
public import Symconf93.AffineConstantLine625
public import Symconf93.AffineCount625

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators
set_option maxHeartbeats 2500000

theorem highLift_injective : Function.Injective highLift := by
  unfold Function.Injective
  decide +kernel

@[simp] theorem highLift_zero : highLift 0 = 0 := by decide +kernel

/-- Unconditional exact contrast transport for the original rank-one Gram
form, reducing 625-degree ambient variables to its genuine H-kernel at
modulus 25. Possible cycle arithmetic is a separate proof. -/
theorem original_rank_one_contrast625 {ι : Type*} [Fintype ι]
    (h93 : Fintype.card ι=93) (h : ι→ι→ZMod 625)
    (hs : ∀ i j,h i j=h j i) (hr : ∀ i,(∑j,h i j)=7) :
    (Nat.card {x : ι→ZMod 625 // quad (withOnes h) x=0}:ℤ) -
      (Nat.card {x : ι→ZMod 625 // quad (withOnes h) x=125}:ℤ) =
    (25:ℤ)^93 * (5 *
      ((Nat.card {a : ι→ZMod 25 //
         action (fun i j=>lowReduce (h i j)) a=0 ∧ quad h (fun i=>lowCast (a i))=0}:ℤ) -
       (Nat.card {a : ι→ZMod 25 //
         action (fun i j=>lowReduce (h i j)) a=0 ∧ quad h (fun i=>lowCast (a i))=125}:ℤ))) := by
  let hl (i j : ι) := lowReduce (h i j)
  have hls (i j : ι) : hl i j=hl j i := congrArg lowReduce (hs i j)
  have hlr (i : ι) : (∑ j,hl i j)=7 := by
    change (∑ j,lowReduce (h i j))=7
    rw [←map_sum,hr]
    decide
  have gs (i j : ι) : withOnes h i j=withOnes h j i := by simp [withOnes,hs i j]
  let Gk := {a : ι→ZMod 25 // action (withOnes hl) a=0}
  let Hk := {a : ι→ZMod 25 // action hl a=0}
  have K (a : ι→ZMod 25) : derivative (withOnes h) (fun i=>lowCast (a i))=0 ↔
       action (withOnes hl) a=0 := by
    rw [derivative_zero_iff_kernel]
    constructor
    · intro A; funext j
      have e := A j
      change action (withOnes hl) a j=0
      simpa only [action,withOnes,map_add,map_one,hl,hs,mul_comm] using e
    · intro A j
      have e := congrFun A j
      change action (withOnes hl) a j=0 at e
      simpa only [action,withOnes,map_add,map_one,hl,hs,mul_comm] using e
  let E : Gk ≃ Hk×ZMod 25 := kernel_rank_one_split h93 hl hls hlr
  let qH (a : Hk) := quad h (fun i=>lowCast (a.val i))
  let qG (a : Gk) := quad (withOnes h) (fun i=>lowCast (a.val i))
  have transportG (t : ZMod 625) :
      Nat.card {a : ι→ZMod 25 //
        derivative (withOnes h) (fun i=>lowCast (a i))=0 ∧
        quad (withOnes h) (fun i=>lowCast (a i))=t} =
      Nat.card {p : Hk×ZMod 25 // qH p.1+lineNorm p.2=t} := by
    let e0 : {a : ι→ZMod 25 //
        derivative (withOnes h) (fun i=>lowCast (a i))=0 ∧
        quad (withOnes h) (fun i=>lowCast (a i))=t} ≃ {a : Gk // qG a=t} :=
      { toFun := fun a=>⟨⟨a.val,(K a.val).mp a.property.1⟩,a.property.2⟩
        invFun := fun a=>⟨a.val.val,⟨(K a.val.val).mpr a.val.property,a.property⟩⟩
        left_inv := by intro a;rfl
        right_inv := by intro a;rfl }
    let e1 : {p : Hk×ZMod 25 // qH p.1+lineNorm p.2=t} ≃ {a : Gk // qG a=t} :=
      E.symm.subtypeEquiv (fun p=>by
        have step := rank_one_stationary_norm h93 h hs hr p.1.val p.1.property p.2
        change qH p.1+lineNorm p.2=t ↔ quad (withOnes h) (fun i=>lowCast (p.1.val i+p.2))=t
        rw [step]
        rfl)
    exact Nat.card_congr (e0.trans e1.symm)
  have transportH (t : ZMod 625) :
      Nat.card {a : Hk // qH a=t} = Nat.card {a : ι→ZMod 25 //
         action hl a=0 ∧ quad h (fun i=>lowCast (a i))=t} := by
    exact Nat.card_congr
      { toFun := fun a => ⟨a.val.val,⟨a.val.property,a.property⟩⟩
        invFun := fun a => ⟨⟨a.val,a.property.1⟩,a.property.2⟩
        left_inv := by intro a;rfl
        right_inv := by intro a;rfl }
  rw [affine_contrast_to_stationary (withOnes h) gs,transportG,transportG,h93]
  classical
  haveI : Fintype Hk := inferInstance
  rw [rankOne_constant_line_contrast qH,transportH,transportH]

#print axioms highLift_injective
#print axioms original_rank_one_contrast625
end Symconf93.AffineFiber625
