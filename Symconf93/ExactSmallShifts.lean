module
public import Symconf93.GramSign93
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Concrete 49/625 low-digit coset shifts. These are exhaustively checked
by the Lean kernel as scalar tables, not assumed prime arithmetic. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def inverseUnitSmall (p u : ℕ) : ℕ :=
  ((List.range p).find? (fun v => (u*v)%p==1)).getD 0

def tag49 : ZMod 49 →+ ZMod 49 where
  toFun a := 7*a
  map_zero' := mul_zero _
  map_add' := mul_add _

def shift49 (tag : ZMod 49) : ZMod 49 :=
  ((7*inverseUnitSmall 7 (2*(tag.val/7)) : ℕ):ZMod 49)

def tag625 : ZMod 625 →+ ZMod 625 where
  toFun a := 25*a
  map_zero' := mul_zero _
  map_add' := mul_add _

def shift625 (tag : ZMod 625) : ZMod 625 :=
  let z := tag.val/25
  if z%5=0 then ((25*inverseUnitSmall 5 (2*(z/5)) : ℕ):ZMod 625)
  else ((125*inverseUnitSmall 5 (2*z) : ℕ):ZMod 625)

theorem tag49_zero_exact : ∀ a : ZMod 49,
    tag49 a=0 → a=7*((a.val/7:ℕ):ZMod 49) := by decide +kernel

theorem tag625_zero_exact : ∀ a : ZMod 625,
    tag625 a=0 → a=25*((a.val/25:ℕ):ZMod 625) := by decide +kernel

theorem shift49_same_tag : ∀ a : ZMod 49, tag49 (shift49 a)=0 := by decide +kernel

theorem shift625_same_tag : ∀ a : ZMod 625, tag625 (shift625 a)=0 := by decide +kernel

theorem shift49_norm_step : ∀ a : ZMod 49, tag49 a≠0 →
    2*a*shift49 (tag49 a)+shift49 (tag49 a)*shift49 (tag49 a)=7 := by decide +kernel

theorem shift625_norm_step : ∀ a : ZMod 625, tag625 a≠0 →
    2*a*shift625 (tag625 a)+shift625 (tag625 a)*shift625 (tag625 a)=125 := by decide +kernel

section N
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem prime49_gram_contrast (A M : Matrix ι ι (ZMod 49))
    (hm : Aᵀ*M=(7:ZMod 49) • (1:Matrix ι ι (ZMod 49)))
    (hi : 0≤contrast (coordinateNorm (ι:=ι)) (7:ZMod 49)) :
    0≤contrast (gramNorm (A*Aᵀ)) (7:ZMod 49) :=
  gram_contrast_nonneg_of_scaled_image A M 7 hm tag49 shift49 7
    (fun a h => ⟨(a.val/7:ℕ),tag49_zero_exact a h⟩)
    shift49_same_tag shift49_norm_step hi

theorem prime625_gram_contrast (A M : Matrix ι ι (ZMod 625))
    (hm : Aᵀ*M=(25:ZMod 625) • (1:Matrix ι ι (ZMod 625)))
    (hi : 0≤contrast (coordinateNorm (ι:=ι)) (125:ZMod 625)) :
    0≤contrast (gramNorm (A*Aᵀ)) (125:ZMod 625) :=
  gram_contrast_nonneg_of_scaled_image A M 25 hm tag625 shift625 125
    (fun a h => ⟨(a.val/25:ℕ),tag625_zero_exact a h⟩)
    shift625_same_tag shift625_norm_step hi

end N
end Symconf93

#print axioms Symconf93.shift49_norm_step
#print axioms Symconf93.shift625_norm_step
#print axioms Symconf93.prime49_gram_contrast
#print axioms Symconf93.prime625_gram_contrast
